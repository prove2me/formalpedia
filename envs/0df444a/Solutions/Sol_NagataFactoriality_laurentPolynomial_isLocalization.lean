-- Prove2me | solution 1 for NagataFactoriality.laurentPolynomial_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:46.773407+00:00
-- url     : https://prove2.me/submissions/9d76dbbf-5893-4950-81d5-06de716deea1

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
theorem _root_.solution (R : Type*) [CommSemiring R] :
    IsLocalization.Away (X : R[X]) R[T;T⁻¹] :=
  LaurentPolynomial.isLocalization
end NagataFactoriality
