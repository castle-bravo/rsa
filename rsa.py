#!/usr/bin/env python3
'''
file:     rsa.py

title:    RSA Cryptosystem Implementation

author:   Alexander Gosselin

e-mail:   alexandergosselin@gmail.com
          alexander.gosselin@alumni.ubc.ca

date:     January 30, 2016 (version 0.0)

license:  GNU GPL v3 <http://www.gnu.org/licenses/gpl-3.0.en.html>

disclaimer:
  I made this for fun, not to secure your communications.
  You can use this program for fun, but do not expect it to make your
  communications secure from eavesdroppers. If you get in trouble
  because this software didn't make your communications secure, It's
  not my problem.

to do:
  1.  Implement a working password protection system for private keys.
      My best idea at the moment is to hash the password to the same
      size as the private key b, and XOR the hashed password with b to
      generate a stored version.
  2.  The encrypt/decrypt functions are pretty hacky. One possible
      improvement would be to compress files using a utility like gzip
      or tar, and encrypt the compressed file. Careful selection and
      implementation of a padding scheme is necessary for this to work.
  3.  Implementation of a real padding scheme. Currently I am just
      appending spaces to the end of the bytestring. This is fine for
      text files, but is not appropriate for binary files.
  4.  Support encryption of arbitrary-sized binary files.

reference:
  RSA Cryptosystem
    <https://en.wikipedia.org/wiki/RSA_%28cryptosystem%29>
  Note: I have tried to use the same variable names
'''

import math
import random
import multiprocessing
import json
import datetime
import functools
import operator
import os

def miller_rabin(n, k=16):
  """
  Miller-Rabin primality test.
  <https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test>
  """
  # factor n - 1 into d*2^r
  f = lambda x, y: (x, y) if y % 2 else f(x + 1, y >> 1)
  r, d = f(0, n - 1)
  # witness loop
  for i in range(k):
    # generate odd random witness
    a = random.randrange(2, n - 2) | 1
    x = pow(a, d, n)
    if x == 1 or x == n - 1: 
      continue
    for j in range(r - 1):
      x = pow(x, 2, n)
      if x == 1: 
        return False
      if x == n - 1: 
        break # bypasses else statement below
    else:
      return False
  return True

def generate_prime(bits=1024, k=None):
  """
  Generate a large prime by checking random bits for primality.
  """
  # k is the security parameter. The higher k, the more certain that
  # generate_prime returns a genuine prime.
  if k is None:
    k = math.ceil(math.log(bits, 2))
  while True:
    x = random.getrandbits(bits) | 2**(bits - 1) + 1
    # note: one or more Fermat tests may disqualify some composite
    #       numbers more efficiently than Miller-Rabin alone.
    #       <https://en.wikipedia.org/wiki/Fermat_primality_test> 
    if miller_rabin(x, k):
      return x

def generate_prime_parallel(bits=1024, k=None, n_processes=2):
  """
  Generate a large prime using multiple processes in parallel.
  Child processes are terminated when any one of them finds a prime.
  """
  workers = []
  results = multiprocessing.Queue()
  for i in range(n_processes):
    process = multiprocessing.Process(
        target = lambda q, kwargs: q.put(generate_prime(**kwargs)),
        args   = (results, { 'bits' : bits, 'k' : k }))
    process.start()
    workers.append(process)
  x = results.get()
  for process in workers:
    process.terminate()
  return x

def modular_multiplicative_inverse(a, n):
  """
  Uses extended euclidean algorithm:
  <https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm>
  """
  t, nt = 0, 1
  r, nr = n, a
  while nr is not 0:
    q = r//nr
    t, nt = nt, t - q*nt
    r, nr = nr, r - q*nr
  if r > 1: return None # a is not invertible modulo n
  if t < 0: return t + n
  return t

def generate_keys(name=None, bits=2048, k=None, parallel=False,
                  n_processes=2):
  """
  Generate and save a public-private RSA keypair.
  """
  if parallel:
    p = generate_prime_parallel(bits//2, k, n_processes)
    q = generate_prime_parallel(bits//2, k, n_processes)
  else:
    p = generate_prime(bits//2, k)
    q = generate_prime(bits//2, k)
    
  n = p*q
  e = 65537 # see: <http://crypto.stackexchange.com/q/3110>
  d = modular_multiplicative_inverse(e, n - p - q + 1)
  
  date = datetime.datetime.now()
  
  public = {
      'n' : n,
      'e' : e,
      # add additional fields here
      'type' : 'public',
      'date' : date.isoformat(),
      'bits' : bits
    }
  
  private = {
      'n' : n,
      'd' : d,
      # add additional fields here (password protection not implemented)
      'type' : 'private',
      'date' : date.isoformat(),
      'bits' : bits
      # hash function, hashed b, is_password_protected : True/False
    }
  
  # save keys in two separate files
  if name is None:
    # name the keys according to the date and time of creation
    name = date.strftime('%Y%m%dT%H%M%S')

  with open(name + '.public', 'w') as public_key:
    json.dump(public, public_key)
  
  with open(name + '.private', 'w') as private_key:
    json.dump(private, private_key)
  
  return

def encode(message, block_size):
  """
  Encodes a text string message as a list of integers no larger than 
  block_size bytes. The end of message is padded with spaces to
  ensure that the length of m is evenly divisible by block_size. 
  """
  if type(message) is str:
    message = message.encode()
  elif type(message) is not bytes:
    print('Error: type of message must be either str or bytes.')
    return
  
  return list(map(
      lambda x: int.from_bytes(x, byteorder='big'),
      (lambda y: y[:-1] + [y[-1].ljust(block_size, b' ')])\
      ([message[i*block_size : (i + 1)*block_size] \
        for i in range(math.ceil(len(message)/block_size))])))

def decode(m, block_size):
  """
  Decodes a list of integers into a text string.
  """
  return functools.reduce(
      operator.add, 
      map(lambda x: x.to_bytes(block_size, byteorder='big').decode(),
          m))

def encrypt(plainfile, keyfile, filename=None):
  """
  Encrypt filename using a public key.
  """
  '''if not key.endswith('public'):
    print('Error: use a public key to encrypt messages.')
    return'''
  with open(keyfile, 'r') as public_key:
    public = json.loads(public_key.read())
  # In future versions, block_size will be calculated according to the
  # specification of a more robust padding scheme.
  with open(plainfile, 'rb') as plaintext:
    m = encode(plaintext.read(), math.ceil(public['bits']/8))
  c = list(map(lambda x: pow(x, public['e'], public['n']), m))
  if filename is None:
    # This could also be filename without extension.
    filename = datetime.datetime.now().strftime('%Y%m%dT%H%M%S')
  # This absolutely needs to be changed in the future.
  # Ciphertext should be stored as a binary file, not text integers in
  # a JSON file.
  with open(filename, 'w') as cyphertext:
    json.dump(c, cyphertext)
  return
 
def decrypt(cipherfile, keyfile, filename=None):
  """
  Decrypt filename using a private key.
  """
  '''if not key.endswith('public'):
    print('Error: use a private key to decrypt cyphertext.')
    return'''
  with open(keyfile, 'r') as private_key:
    private = json.loads(private_key.read())
  # This absolutely needs to be changed in the future.
  # Ciphertext should be stored as a binary file, not text integers in
  # a JSON file.
  with open(cipherfile, 'r') as ciphertext:
    c = json.loads(ciphertext.read())
  m = list(map(lambda x: pow(x, private['d'], private['n']), c))
  message = decode(m, math.floor(private['bits']/8))
  if filename is None:
    # This could also be filename with text extension.
    filename = datetime.datetime.now().strftime('%Y%m%dT%H%M%S') + '.txt'
  with open(filename, 'w') as plainfile:
    plainfile.write(message)
  return

def main(args):
  if args.subparser_name == 'generate-keys':
    generate_keys(args.name, args.bits, args.k, args.parallel,
                  args.n_threads)
    return
  if args.subparser_name == 'encrypt': 
    encrypt(args.plainfile, args.key, args.filename)
    return
  if args.subparser_name == 'decrypt':
    decrypt(args.cipherfile, args.key, args.filename)
    return

if __name__ == '__main__':
  
  import sys
  import argparse
  
  parser = argparse.ArgumentParser(
      prog='rsa',
      description='Alex\'s implementation of the RSA cryptosystem.')
  subparsers = parser.add_subparsers(
      dest='subparser_name',
      help='sub-command --help')
  
  parser_gen = subparsers.add_parser('generate-keys',
      help='generate an RSA keypair')
  parser_gen.add_argument('-b', '--bits',
      dest='bits',
      type=int,
      default=2048,
      help='Key size. Default is 2048 bits.')
  parser_gen.add_argument('-k',
      dest='k',
      type=int,
      default=None,
      help='Security parameter for Miller-Rabin primality test.')
  parser_gen.add_argument('--name',
      dest='name',
      type=str,
      default=None,
      help='Name attached to key files. Default is current datetime.')
  parser_gen.add_argument('-p', '--parallel',
      action='store_true',
      help='Use multiple processes to generate large primes faster.')
  parser_gen.add_argument('-n', '--n-threads',
      dest='n_threads',
      type=int,
      default=2,
      help='Number of threads to use if parallel mode is turned on. ' +
           'Don\'t use more threads than you have available on your ' +
           'machine. Default number is 2.')
      
  parser_enc = subparsers.add_parser('encrypt',
      help='Encrypt plaintext using a public key.')
  parser_enc.add_argument('plainfile',
      type=str,
      help='File to encrypt.')
  parser_enc.add_argument('key',
      type=str,
      help='File containing a public key.')
  parser_enc.add_argument('-o',
      dest='filename',
      type=str,
      default=None,
      help='Filename for encrypted file. Default is current datetime.')
  
  parser_dec = subparsers.add_parser('decrypt',
      help='Decrypt file using a private key')
  parser_dec.add_argument('cipherfile',
      type=str,
      help='File to decrypt.')
  parser_dec.add_argument('key',
      type=str,
      help='File containing a private key.')
  parser_dec.add_argument('-o',
      dest='filename',
      type=str,
      default=None,
      help='Filename for decrypted file. Default is current datetime.')
      
  args = parser.parse_args(sys.argv[1:])
  
  main(args)
