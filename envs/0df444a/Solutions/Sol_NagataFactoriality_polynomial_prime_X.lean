-- Prove2me | solution 1 for NagataFactoriality.polynomial_prime_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:49.442919+00:00
-- url     : https://prove2.me/submissions/213119b5-da52-412c-b2d5-37c9309ccf60

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_Laurent

set_option autoImplicit false
open NagataFactoriality
open scoped LaurentPolynomial
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] :
    Prime (Polynomial.X : R[X]) :=
  (Polynomial.prime_X : Prime (Polynomial.X : R[X]))
end NagataFactoriality
