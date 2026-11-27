-- Prove2me | solution 1 for GroundTheory.FunctionField.IsFunctionField.of_functionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:06.030845+00:00
-- url     : https://prove2.me/submissions/65bf5072-23aa-4921-82bf-cb21ee6d8c33

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
open scoped Polynomial
omit [Algebra k K]
namespace GroundTheory.FunctionField.Place
namespace _root_.GroundTheory.FunctionField.IsFunctionField
theorem _root_.solution [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    IsFunctionField k K := by
  have := essFiniteType_ratFunc (k := k)
  have : Algebra.EssFiniteType k K := .comp k (RatFunc k) K
  apply IsFunctionField.of_trdeg_eq_one
  have h := lift_trdeg_add_eq k (RatFunc k) K
  rw [trdeg_eq_one (k := k) (K := RatFunc k), trdeg_eq_zero, Cardinal.lift_zero, add_zero,
    Cardinal.lift_one] at h
  exact (Cardinal.lift_eq_one.1 h.symm)
end _root_.GroundTheory.FunctionField.IsFunctionField
end GroundTheory.FunctionField.Place
