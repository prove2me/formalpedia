-- Prove2me | solution 1 for NagataFactoriality.int_polynomial_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:37.795865+00:00
-- url     : https://prove2.me/submissions/b2142c5f-b20f-4b92-b0f6-cee28cb14077

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution : UniqueFactorizationMonoid ℤ[X] := by
  infer_instance
end NagataFactoriality
