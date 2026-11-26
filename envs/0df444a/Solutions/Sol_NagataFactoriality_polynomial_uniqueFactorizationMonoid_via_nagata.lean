-- Prove2me | solution 1 for NagataFactoriality.polynomial_uniqueFactorizationMonoid_via_nagata
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:13.35893+00:00
-- url     : https://prove2.me/submissions/149361d2-f8e9-41b1-8a3a-9e2804106ecd

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_Laurent
import Theorems.Thm_NagataFactoriality_laurentPolynomial_uniqueFactorizationMonoid
import Theorems.Thm_NagataFactoriality_polynomial_uniqueFactorizationMonoid_of_laurent

set_option autoImplicit false
open NagataFactoriality
open scoped LaurentPolynomial
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by
  letI : UniqueFactorizationMonoid R[T;T⁻¹] := laurentPolynomial_uniqueFactorizationMonoid (R := R)
  exact polynomial_uniqueFactorizationMonoid_of_laurent (R := R)
end NagataFactoriality
