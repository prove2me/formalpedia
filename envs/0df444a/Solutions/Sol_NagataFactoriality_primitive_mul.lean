-- Prove2me | solution 1 for NagataFactoriality.primitive_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:11.293019+00:00
-- url     : https://prove2.me/submissions/13916b79-e455-412b-8a94-a04156b3d5c9

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Gauss

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [StrongNormalizedGCDMonoid R]
    {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive :=
  hp.mul hq
end NagataFactoriality
