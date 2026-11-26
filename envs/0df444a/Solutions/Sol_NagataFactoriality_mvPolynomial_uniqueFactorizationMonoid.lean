-- Prove2me | solution 1 for NagataFactoriality.mvPolynomial_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:40.603748+00:00
-- url     : https://prove2.me/submissions/e3424430-de2e-468a-b66b-baafca61600b

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution (n : ℕ) (k : Type*) [Field k] :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) k) := by
  infer_instance
end NagataFactoriality
