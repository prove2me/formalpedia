-- Prove2me | solution 1 for NagataFactoriality.int_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:17.794798+00:00
-- url     : https://prove2.me/submissions/6b63e3ca-3b8b-4f44-a4c3-dd6d41568841

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Applications_Examples

set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution : UniqueFactorizationMonoid ℤ := by
  infer_instance
end NagataFactoriality
