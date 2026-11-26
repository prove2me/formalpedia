-- Prove2me | solution 1 for NagataFactoriality.polynomial_content_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:10.553814+00:00
-- url     : https://prove2.me/submissions/2fe53a7a-651d-4f5b-9ff6-be148f48cd82

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Gauss

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [StrongNormalizedGCDMonoid R]
    (p q : R[X]) : (p * q).content = p.content * q.content :=
  Polynomial.content_mul
end NagataFactoriality
