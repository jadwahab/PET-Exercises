#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 04
#
# Zero Knowledge Proofs
#
# Run the tests through:
# $ py.test -v test_file_name.py

###########################
# Group Members: Jad Wahab
###########################

from petlib.ec import EcGroup
from petlib.bn import Bn

from hashlib import sha256
from binascii import hexlify

def setup():
    """ Generates the Cryptosystem Parameters. """
    G = EcGroup(nid=713)
    g = G.hash_to_point(b"g")
    hs = [G.hash_to_point(("h%s" % i).encode("utf8")) for i in range(4)]
    o = G.order()
    return (G, g, hs, o)

def keyGen(params):
   """ Generate a private / public key pair. """
   (G, g, hs, o) = params
   priv = o.random()
   pub = priv * g
   return (priv, pub)

def to_challenge(elements):
    """ Generates a Bn challenge by hashing a number of EC points """
    Cstring = b",".join([hexlify(x.export()) for x in elements])
    Chash =  sha256(Cstring).digest()
    return Bn.from_binary(Chash)

#####################################################
# TASK 1 -- Prove knowledge of a DH public key's
#           secret.

def proveKey(params, priv, pub):
    """ Uses the Schnorr non-interactive protocols produce a proof
        of knowledge of the secret priv such that pub = priv * g.

        Outputs: a proof (c, r)
                 c (a challenge)
                 r (the response)
    """
    (G, g, hs, o) = params
    ## YOUR CODE HERE:
    #Generate random w
    w = o.random()
    #Calculate W
    W = w*g
    #Calculate challenge
    c = to_challenge([g,W])
    #Generate response
    r = (w - c*priv) % o
    return (c, r)

def verifyKey(params, pub, proof):
    """ Schnorr non-interactive proof verification of knowledge of a a secret.
        Returns a boolean indicating whether the verification was successful.
    """
    (G, g, hs, o) = params
    c, r = proof
    gw_prime  = c * pub + r * g
    return to_challenge([g, gw_prime]) == c

#####################################################
# TASK 2 -- Prove knowledge of a Discrete Log
#           representation.

def commit(params, secrets):
    """ Produces a commitment C = r * g + Sum xi * hi,
        where secrets is a list of xi of length 4.
        Returns the commitment (C) and the opening (r).
    """
    assert len(secrets) == 4
    (G, g, (h0, h1, h2, h3), o) = params
    x0, x1, x2, x3 = secrets
    r = o.random()
    C = x0 * h0 + x1 * h1 + x2 * h2 + x3 * h3 + r * g
    return (C, r)

def proveCommitment(params, C, r, secrets):
    """ Prove knowledge of the secrets within a commitment,
        as well as the opening of the commitment.

        Args: C (the commitment), r (the opening of the
                commitment), and secrets (a list of secrets).
        Returns: a challenge (c) and a list of responses.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    x0, x1, x2, x3 = secrets

    ## YOUR CODE HERE:

    # First generate random witnesses for each secret plus the opening of the commitment r
    w = [o.random() for i in range(5)]  # Need 5 to cater for the 4 secrets plus the opening of the commitment r

    # Then compute Cw by performing the same operation as per the commitment C, but replacing the secrets and r by their witnesses generated above
    Cw = w[0] * h0 + w[1] * h1 + w[2] * h2 + w[3] * h3 + w[4] * g

    # Generates a Bn challenge by hashing the EC points g, h0, h1, h2, h3 and Cw
    c = to_challenge([g, h0, h1, h2, h3, Cw])

    # Calculate the corresponding responses to the above challenge for each secret and the opening of the commitment r
    r0 = (w[0] - (c * x0)) % o
    r1 = (w[1] - (c * x1)) % o
    r2 = (w[2] - (c * x2)) % o
    r3 = (w[3] - (c * x3)) % o
    rr = (w[4] - (c * r)) % o
    responses = (r0, r1, r2, r3, rr)

    return (c, responses)

def verifyCommitments(params, C, proof):
    """ Verify a proof of knowledge of the commitment.
        Return a boolean denoting whether the verification succeeded. """
    (G, g, (h0, h1, h2, h3), o) = params
    c, responses = proof
    (r0, r1, r2, r3, rr) = responses

    Cw_prime = c * C + r0 * h0 + r1 * h1 + r2 * h2 + r3 * h3 + rr * g
    c_prime = to_challenge([g, h0, h1, h2, h3, Cw_prime])
    return c_prime == c


#####################################################
# TASK 3 -- Prove Equality of discrete logarithms.
#

def gen2Keys(params):
    """ Generate two related public keys K = x * g and L = x * h0. """
    (G, g, (h0, h1, h2, h3), o) = params
    x = o.random()

    K = x * g
    L = x * h0

    return (x, K, L)

def proveDLEquality(params, x, K, L):
    """ Generate a ZK proof that two public keys K, L have the same secret private key x,
        as well as knowledge of this private key. """
    (G, g, (h0, h1, h2, h3), o) = params
    w = o.random()
    Kw = w * g
    Lw = w * h0

    c = to_challenge([g, h0, Kw, Lw])

    r = (w - c * x) % o
    return (c, r)

def verifyDLEquality(params, K, L, proof):
    """ Return whether the verification of equality of two discrete logarithms succeeded. """
    (G, g, (h0, h1, h2, h3), o) = params
    c, r = proof
    #Recover Kw from c and r
    P1 = r*g + c*K
    #Recover Lw from c and r
    P2 = r*h0 + c*L

    c_prime = to_challenge([g,h0,P1,P2])

    return c_prime == c

#####################################################
# TASK 4 -- Prove correct encryption and knowledge of
#           a plaintext.

def encrypt(params, pub, m):
    """ Encrypt a message m under a public key pub.
        Returns both the randomness and the ciphertext.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    k = o.random()
    return k, (k * g, k * pub + m * h0)

def proveEnc(params, pub, Ciphertext, k, m):
    """ Prove in ZK that the ciphertext is well formed
        and knowledge of the message encrypted as well.

        Return the proof: challenge and the responses.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext

    ## YOUR CODE HERE:

    # First generate some random witnesses for the secrets k and m
    wk = o.random()
    wm = o.random()

    # Then compute the 2 commitments corresponding to the 2 parts a and b of the ciphertext, substituting k and m by wk and wm
    Wa = wk * g
    Wb = wk * pub + wm * h0

    # Compute the corresponding challenge
    c = to_challenge([g, h0, pub, a, b, Wa, Wb])

    #compute the corresponding responses
    rk = (wk - (c * k)) % o
    rm = (wm - (c * m)) % o

    return (c, (rk, rm))

def verifyEnc(params, pub, Ciphertext, proof):
    """ Verify the proof of correct encryption and knowledge of a ciphertext. """
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext
    (c, (rk, rm)) = proof

    ## YOUR CODE HERE:
    # Compute the following Wa_prime and Wb_prime that we will use to check the challenge
    Wa_prime = rk * g + c * a
    Wb_prime = rk * pub + rm * h0 + c * b
    # Compute the challenge based on the above
    c_prime = to_challenge([g, h0, pub, a, b, Wa_prime, Wb_prime])

    return c_prime == c ## YOUR RETURN HERE

#####################################################
# TASK 5 -- Prove a linear relation
#

def relation(params, x1):
    """ Returns a commitment C to x0 and x1, such that x0 = 10 x1 + 20,
        as well as x0, x1 and the commitment opening r.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    r = o.random()

    x0 = (10 * x1 + 20)
    C = r * g + x1 * h1 + x0 * h0

    return C, x0, x1, r

def prove_x0eq10x1plus20(params, C, x0, x1, r):
    """ Prove C is a commitment to x0 and x1 and that x0 = 10 x1 + 20. """
    (G, g, (h0, h1, h2, h3), o) = params

    #Generate one w for each secret x1,r for the commitment written as C' = C - 20h = g*r + h1*x1 + 10*x1*h0
    w1 = o.random()
    wr = o.random()
    #Generate one W1 for linear equality and one Wc for commitment
    Wc = wr*g + w1*h1 + 10*w1*h0
    c = to_challenge([g,h0,h1,C,Wc])
    #Generate one response for every w
    r1 = w1 - c*x1
    rr = wr - c*r
    return (c,(r1,rr))

def verify_x0eq10x1plus20(params, C, proof):
    """ Verify that proof of knowledge of C and x0 = 10 x1 + 20. """
    (G, g, (h0, h1, h2, h3), o) = params

    (c,(r1,rr)) = proof
    #Recover C' = C - 20h
    C_prime = rr*g + r1*h1 + 10*r1*h0 + c*(C-20*h0)
    c_prime = to_challenge([g,h0,h1,C,C_prime])
    return c_prime == c

#####################################################
# TASK 6 -- (OPTIONAL) Prove that a ciphertext is either 0 or 1


def binencrypt(params, pub, m):
    """ Encrypt a binary value m under public key pub """
    assert m in [0, 1]
    (G, g, (h0, h1, h2, h3), o) = params

    k = o.random()
    return k, (k * g, k * pub + m * h0)

def provebin(params, pub, Ciphertext, k, m):
    """ Prove a ciphertext is valid and encrypts a binary value either 0 or 1. """

    # Retrieve params and elements of the ciphertext
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext

    # Commit to m
    r = o.random()  # r is used for the opening of the commitment
    Cm = m * g + r * h1

    # Commit to m being either 0 or 1. In this case m(1-m) = 0 <=> Cm^(1-m) = g^(m(1-m)) * h1^(r(1-m)) <=> Cm = Cm^m * h1^(r(1-m))
    rbin = o.random()
    Cmbin = m * Cm + rbin * h1

    # First generate some random witnesses for the secrets k and m, and the openings of the commitments r and rbin
    wk = o.random()
    wm = o.random()
    wr = o.random()
    wrbin = o.random()

    # Then compute the 4 commitments corresponding to the 2 parts a and b of the ciphertext, m and the fact that m is either 0 or 1 (m(1-m)=0), substituting k, m, r and rbin by wk, wm, wr and wrbin respectively
    Wa = wk * g
    Wb = wk * pub + wm * h0
    WCm = wm * g + wr * h1
    WCmbin = wm * Cm + wrbin * h1

    # Compute the corresponding challenge
    c = to_challenge([g, h0, h1, pub, a, b, Cm, Wa, Wb, WCm, WCmbin])

    #compute the corresponding responses
    rk = (wk - (c * k)) % o
    rm = (wm - (c * m)) % o
    rr = (wr - (c * r)) % o
    rrbin = (wrbin - (c * rbin)) % o

    return (Cm, Cmbin, c, (rk, rm, rr, rrbin))

def verifybin(params, pub, Ciphertext, proof):
    """ verify that proof that a ciphertext is a binary value 0 or 1. """

    # Retrieve params and elements of the ciphertext and the proof
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext
    (Cm, Cmbin, c, (rk, rm, rr, rrbin)) = proof

    # Compute the following Wa_prime, Wb_prime, WCm_prime and WCmbin_prime that we will use to check the challenge
    Wa_prime = rk * g + c * a
    Wb_prime = rk * pub + rm * h0 + c * b
    WCm_prime = rm * g + rr * h1 + c * Cm
    WCmbin_prime = rm * Cm + rrbin * h1 + c * Cmbin

    # Compute the challenge based on the above
    c_prime = to_challenge([g, h0, h1, pub, a, b, Cm, Wa_prime, Wb_prime, WCm_prime, WCmbin_prime])

    return c_prime == c

def test_bin_correct():
    """ Test that a correct proof verifies """

    params = setup()

    priv, pub = keyGen(params)

    # Encrypt and prove the message is 0
    k0, ciphertext0 = binencrypt(params, pub, 0)
    proof0 = provebin(params, pub, ciphertext0, k0, 0)

    # Encrypt and prove the message is 1
    k1, ciphertext1 = binencrypt(params, pub, 1)
    proof1 = provebin(params, pub, ciphertext1, k1, 1)

    assert verifybin(params, pub, ciphertext0, proof0)
    assert verifybin(params, pub, ciphertext1, proof1)

def test_bin_incorrect():
    """ Prove that incorrect proofs fail. """

    params = setup()

    priv, pub = keyGen(params)

    # Encrypt and prove the message is 0
    k0, ciphertext0 = binencrypt(params, pub, 0)
    proof0 = provebin(params, pub, ciphertext0, k0, 0)

    # Encrypt and prove the message is 1
    k1, ciphertext1 = binencrypt(params, pub, 1)
    proof1 = provebin(params, pub, ciphertext1, k1, 1)

    assert not verifybin(params, pub, ciphertext0, proof1)
    assert not verifybin(params, pub, ciphertext1, proof0)


#####################################################
# TASK Q1 - Answer the following question:
#
# The interactive Schnorr protocol (See PETs Slide 8) offers
# "plausible deniability" when performed with an
# honest verifier. The transcript of the 3 step interactive
# protocol could be simulated without knowledge of the secret
# (see Slide 12). Therefore the verifier cannot use it to prove
# to a third party that the holder of secret took part in the
# protocol acting as the prover.
#
# Does "plausible deniability" hold against a dishonest verifier
# that  deviates from the Schnorr identification protocol? Justify
# your answer by describing what a dishonest verifier may do.

""" TODO: Your answer here. """
""" No, plausible deniability does not necessarily hold against a dishonest verifier. For example a dishonest verifier could deviate from the interactive Schnorr identification protocol by setting the challenge c = H(pub, W), where H is a secure hash function and W the first part of the exchange, instead of setting the challenge c randomly as required by the interactive Schnorr identification protocol. In this case the dishonest verifier turns the interactive Schnorr identification protocol into a signature scheme based on the Fiat-Shamir Heuristic work, which forces causality. Indeed the prover cannot simulate a forged proof anymore by computing a forged W' from a random r' and c' since a prover must first set W' and then c'.
"""

 #####################################################
 # TASK Q2 - Answer the following question:
 #
 # Consider the function "prove_something" below, that
 # implements a zero-knowledge proof on commitments KX
 # and KY to x and y respectively. Note that the prover
 # only knows secret y. What statement is a verifier,
 # given the output of this function, convinced of?
 #
# Hint: Look at "test_prove_something" too.

""" TODO: Your answer here. """
""" The verifier is convinced that the prover knows either secret x or secret y such that KX = g^x, KY = g^y, i.e. the prover can prove either KX or KY. Indeed the prover simulates the proof for the secret s/he doesn't know (x in this case), and then uses that simulation (challenge c1) to perform the proof for the secret s/he knows (y in this case) with the final challenge c = c1 + c2 (mod o), where c1 is simulated and c2 is the challenge for which the ZKP is actually performed.
"""

def prove_something(params, KX, KY, y):
 (G, g, _, o) = params

 # Simulate proof for KX
 # r = wx - cx => g^w = g^r * KX^c
 rx = o.random()
 c1 = o.random()
 W_KX = rx * g + c1 * KX

 # Build proof for KY
 wy = o.random()
 W_KY = wy * g
 c = to_challenge([g, KX, KY, W_KX, W_KY])

 # Build so that: c1 + c2 = c (mod o)
 c2 = (c - c1) % o
 ry = ( wy - c2 * y ) % o

 # return proof
 return (c1, c2, rx, ry)

import pytest

def test_prove_something():
 params = setup()
 (G, g, hs, o) = params

 # Commit to x and y
 x = o.random()
 y = o.random()
 KX = x*g
 KY = y*g

 # Pass only y
 (c1, c2, rx, ry) = prove_something(params, KX, KY, y)

 # Verify the proof
 W_KX = rx * g + c1 * KX
 W_KY = ry * g + c2 * KY
 c = to_challenge([g, KX, KY, W_KX, W_KY])
 assert c % o == (c1 + c2) % o
