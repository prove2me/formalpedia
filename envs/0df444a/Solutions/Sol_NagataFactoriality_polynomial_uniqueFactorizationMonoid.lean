-- Prove2me | solution 1 for NagataFactoriality.polynomial_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:14.766375+00:00
-- url     : https://prove2.me/submissions/011906a4-3658-414f-88fc-1c1c630cff26

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Gauss

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by
  infer_instance
end NagataFactoriality
