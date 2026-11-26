-- Prove2me | solution 1 for NagataFactoriality.iterated_polynomial_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:46.802577+00:00
-- url     : https://prove2.me/submissions/3fe395e3-16df-45d9-9719-2612f5243b2b

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution (k : Type*) [Field k] :
    UniqueFactorizationMonoid (Polynomial (Polynomial k)) := by
  infer_instance
end NagataFactoriality
