#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py

###########################
# Group Members: Jad Wahab
###########################

import pytest

#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can
#           be imported.

import petlib

#####################################################
# TASK 2 -- Symmetric encryption using AES-GCM
#           (Galois Counter Mode)
#
# Implement a encryption and decryption function
# that simply performs AES_GCM symmetric encryption
# and decryption using the functions in petlib.cipher.

from os import urandom
from petlib.cipher import Cipher
from petlib.bn import Bn

def encrypt_message(K, message):
    """ Encrypt a message under a key K """

    plaintext = message.encode("utf8")

    ## YOUR CODE HERE
    iv = urandom(16)

    aes = Cipher("aes-128-gcm")

    ciphertext, tag = aes.quick_gcm_enc(K, iv, plaintext)

    return (iv, ciphertext, tag)

def decrypt_message(K, iv, ciphertext, tag):
    """ Decrypt a cipher text under a key K

        In case the decryption fails, throw an exception.
    """
    ## YOUR CODE HERE
    aes = Cipher("aes-128-gcm")

    plain = aes.quick_gcm_dec(K, iv, ciphertext, tag)

    return plain.encode("utf8")

#####################################################
# TASK 3 -- Understand Elliptic Curve Arithmetic
#           - Test if a point is on a curve.
#           - Implement Point addition.
#           - Implement Point doubling.
#           - Implement Scalar multiplication (double & add).
#           - Implement Scalar multiplication (Montgomery ladder).
#
# MUST NOT USE ANY OF THE petlib.ec FUNCIONS. Only petlib.bn!

from petlib.bn import Bn


def is_point_on_curve(a, b, p, x, y):
    """
    Check that a point (x, y) is on the curve defined by a,b and prime p.
    Reminder: an Elliptic Curve on a prime field p is defined as:

              y^2 = x^3 + ax + b (mod p)
                  (Weierstrass form)

    Return True if point (x,y) is on curve, otherwise False.
    By convention a (None, None) point represents "infinity".
    """
    assert isinstance(a, Bn)
    assert isinstance(b, Bn)
    assert isinstance(p, Bn) and p > 0
    assert (isinstance(x, Bn) and isinstance(y, Bn)) \
           or (x == None and y == None)

    if x is None and y is None:
        return True

    lhs = (y * y) % p
    rhs = (x*x*x + a*x + b) % p
    on_curve = (lhs == rhs)

    return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
    """Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = (yq - yp) * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """

    # ADD YOUR CODE BELOW

    if (x0 is None and y0 is None):
        return (x1, y1)

    if (x1 is None and y1 is None):
        return (x0, y0)

    if (x1 == x0 and y1 == y0):
        raise Exception('EC Points must not be equal')

    if (x1 == x0 and y0 == (p-y1) ):
        return (None, None)

    lam = (y1-y0).mod_mul( (x1-x0).mod_inverse(p), p )
    xr = lam.mod_pow(2, p).mod_sub(x0,p).mod_sub(x1,p)
    yr = lam.mod_mul( (x1-xr), p ).mod_sub(y1,p)

    return (xr, yr)

def point_double(a, b, p, x, y):
    """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = (3 * xp ^ 2 + a) * (2 * yp) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """

    if (x is None and y is None):
        return (x, y)


    # ADD YOUR CODE BELOW
    lam1 = Bn(3).int_mul(x).int_mul(x).int_add(a).mod(p)
    lam2 = Bn(2).mod_mul(y,p).mod_inverse(p)
    lam = lam1.mod_mul(lam2,p)

    xr1 = lam.mod_pow(2,p)
    xr2 = x.mod_mul(Bn(2),p)
    xr = xr1.mod_sub(xr2,p)

    yr1 = lam.mod_mul( (x-xr),p )
    yr = yr1.mod_sub(y,p)

    return xr, yr

def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        Q = infinity
        for i = 0 to num_bits(P)-1
            if bit i of r == 1 then
                Q = Q + P
            P = 2 * P
        return Q

    """
    Q = (None, None)
    P = (x, y)

    for i in range(scalar.num_bits()):
        xq, yq = Q
        xp, yp = P
        if scalar.is_bit_set(i):
            Q = point_add(a, b, p, xp, yp, xq, yq)
        P = point_double(a, b, p, xp, yp)

    return Q

def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        R0 = infinity
        R1 = P
        for i in num_bits(P)-1 to zero:
            if di = 0:
                R1 = R0 + R1
                R0 = 2R0
            else
                R0 = R0 + R1
                R1 = 2 R1
        return R0

    """
    R0 = (None, None)
    R1 = (x, y)

    for i in reversed(range(0,scalar.num_bits())):
        xr0, yr0 = R0
        xr1, yr1 = R1
        if not scalar.is_bit_set(i):
            R1 = point_add(a,b,p,xr0,yr0,xr1,yr1)
            R0 = point_double(a,b,p,xr0,yr0)
        else:
            R0 = point_add(a,b,p,xr0,yr0,xr1,yr1)
            R1 = point_double(a,b,p,xr1,yr1)

    return R0


#####################################################
# TASK 4 -- Standard ECDSA signatures
#
#          - Implement a key / param generation
#          - Implement ECDSA signature using petlib.ecdsa
#          - Implement ECDSA signature verification
#            using petlib.ecdsa

from hashlib import sha256
from petlib.ec import EcGroup
from petlib.ecdsa import do_ecdsa_sign, do_ecdsa_verify

def ecdsa_key_gen():
    """ Returns an EC group, a random private key for signing
        and the corresponding public key for verification"""
    G = EcGroup()
    priv_sign = G.order().random()
    pub_verify = priv_sign * G.generator()
    return (G, priv_sign, pub_verify)


def ecdsa_sign(G, priv_sign, message):
    """ Sign the SHA256 digest of the message using ECDSA and return a signature """
    plaintext =  message.encode("utf8")

    ## YOUR CODE HERE
    digest = sha256(plaintext).digest()
    sig = do_ecdsa_sign(G, priv_sign, digest)

    return sig

def ecdsa_verify(G, pub_verify, message, sig):
    """ Verify the ECDSA signature on the message """
    plaintext =  message.encode("utf8")

    ## YOUR CODE HERE
    digest = sha256(plaintext).digest()
    res = do_ecdsa_verify(G, pub_verify, sig, digest)

    return res

#####################################################
# TASK 5 -- Diffie-Hellman Key Exchange and Derivation
#           - use Bob's public key to derive a shared key.
#           - Use Bob's public key to encrypt a message.
#           - Use Bob's private key to decrypt the message.
#
# NOTE:


def dh_get_key():
    """ Generate a DH key pair """
    G = EcGroup()
    priv_dec = G.order().random()
    pub_enc = priv_dec * G.generator()
    return (G, priv_dec, pub_enc)


def dh_encrypt(pub_rec, message, aliceSig):
    """ Assume you know the public key of someone else (Bob),
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message with Alice's key.
    """

    ## YOUR CODE HERE
    plaintext = message.encode("utf8")

    shared_key = aliceSig[1] * pub_rec
    shared_key = shared_key.export()
    shared_key_fixed = sha256(shared_key).digest()
    shared_key_fixed = shared_key_fixed[:16]

    iv, ciphertext, tag = encrypt_message(shared_key_fixed, plaintext)

    digest = sha256(plaintext).digest()
    sig = do_ecdsa_sign(aliceSig[0], aliceSig[1], digest)

    return (iv, ciphertext, tag, aliceSig[2], sig)


def dh_decrypt(priv, CIPHER, aliceVer):
    """ Decrypt a received message encrypted using your public key,
    of which the private key is provided. Optionally verify
    the message came from Alice using her verification key."""

    ## YOUR CODE HERE
    shared_key = priv * CIPHER[3]
    shared_key = shared_key.export()
    shared_key_fixed = sha256(shared_key).digest()
    shared_key_fixed = shared_key_fixed[:16]

    aes = Cipher("aes-128-gcm")

    try:
        plain = aes.quick_gcm_dec(shared_key_fixed, CIPHER[0], CIPHER[1], CIPHER[2])
    except:
        raise Exception('decryption failed')


    digest = sha256(plain).digest()
    res = do_ecdsa_verify(aliceVer[0], aliceVer[2], CIPHER[4], digest)

    if res == 0:
        raise Exception('decryption failed')

    return (plain.encode("utf8"), res)

## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test-2.7 --cov-report html --cov Lab01Code Lab01Code.py
'''
def test_encrypt():
    assert False

def test_decrypt():
    assert False

def test_fails():
    assert False
'''

@pytest.mark.task5
def test_dh_encrypt():
    """ Tests encryption with DH """

    A_keys = dh_get_key()

    G, priv_B, pub_B = dh_get_key()

    message = u"Hello World!"

    iv, ciphertext, tag, pub_A, sig = dh_encrypt(pub_B, message, A_keys)

    assert len(iv) == 16
    assert len(ciphertext) == len(message)
    assert len(tag) == 16

@pytest.mark.task5
def test_dh_decrypt():
    """ Tests decryption with DH """
    A_keys = dh_get_key()

    G, priv_B, pub_B = dh_get_key()

    message = u"Hello World!"

    #iv, ciphertext, tag, pub_A, sig = dh_encrypt(pub_B, message)
    CIPHER = dh_encrypt(pub_B, message, A_keys)

    assert len(CIPHER[0]) == 16
    assert len(CIPHER[1]) == len(message)
    assert len(CIPHER[2]) == 16

    m, sig = dh_decrypt(priv_B, CIPHER, A_keys)
    assert m == message

    assert sig ==  True

@pytest.mark.task5
def test_dh_fails():
    from pytest import raises

    from os import urandom

    A_keys = dh_get_key()

    G, priv_B, pub_B = dh_get_key()

    message = u"Hello World!"

    #iv, ciphertext, tag, pub_A, sig = dh_encrypt(pub_B, message)
    CIPHER = dh_encrypt(pub_B, message, A_keys)
    #CIPHER[0] -> iv
    #CIPHER[1] -> ciphertext
    #CIPHER[2] -> tag
    #CIPHER[3] -> pub_A
    #CIPHER[4] -> sig

    m, sig = dh_decrypt(priv_B, CIPHER, A_keys)

    #use random iv
    CIPHER1 = [urandom(len(CIPHER[0])), CIPHER[1], CIPHER[2], CIPHER[3], CIPHER[4]]
    with raises(Exception) as excinfo:
        dh_decrypt(priv_B, CIPHER1, A_keys)
    assert 'decryption failed' in str(excinfo.value)

    #use random ciphertext
    CIPHER2 = [CIPHER[0], urandom(len(CIPHER[1])), CIPHER[2], CIPHER[3], CIPHER[4]]
    with raises(Exception) as excinfo:
        dh_decrypt(priv_B, CIPHER2, A_keys)
    assert 'decryption failed' in str(excinfo.value)

    #use random tag
    CIPHER3 = [CIPHER[0], CIPHER[1], urandom(len(CIPHER[2])), CIPHER[3], CIPHER[4]]
    with raises(Exception) as excinfo:
        dh_decrypt(priv_B, CIPHER3, A_keys)
    assert 'decryption failed' in str(excinfo.value)

    #use random public key
    G, priv_rand, pub_rand = dh_get_key()
    CIPHER4 = [CIPHER[0], CIPHER[1], CIPHER[2], pub_rand, CIPHER[4]]
    with raises(Exception) as excinfo:
        dh_decrypt(priv_B, CIPHER4, A_keys)
    assert 'decryption failed' in str(excinfo.value)

    #use random verification key
    G_rand, priv_rand, pub_rand = dh_get_key()
    plaintext = message.encode("utf8")
    digest = sha256(plaintext).digest()
    sig_rand = do_ecdsa_sign(G_rand, priv_rand, digest)
    sig_rand[0].int_add(Bn(3))
    sig_rand[1].int_add(Bn(3))
    CIPHER5 = [CIPHER[0], CIPHER[1], CIPHER[2], CIPHER[3], sig_rand]
    with raises(Exception) as excinfo:
        dh_decrypt(priv_B, CIPHER5, A_keys)
    assert 'decryption failed' in str(excinfo.value)

#####################################################
# TASK 6 -- Time EC scalar multiplication
#             Open Task.
#
#           - Time your implementations of scalar multiplication
#             (use time.clock() for measurements)for different
#              scalar sizes)
#           - Print reports on timing dependencies on secrets.
#           - Fix one implementation to not leak information.

def time_scalar_mul():
    pass
