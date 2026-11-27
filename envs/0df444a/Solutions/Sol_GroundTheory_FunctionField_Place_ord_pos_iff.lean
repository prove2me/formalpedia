-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:54.406153+00:00
-- url     : https://prove2.me/submissions/5878cb9b-01e6-4a31-be1e-01cc8699a19d

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_lt_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution {x : K} (hx : x ≠ 0) : 0 < v.ord x ↔ v.ring.valuation x < 1 := by
  rw [← v.valuation_lt_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  omega
end GroundTheory.FunctionField.Place
