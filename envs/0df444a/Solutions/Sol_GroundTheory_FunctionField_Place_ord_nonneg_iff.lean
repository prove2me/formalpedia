-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:16.599238+00:00
-- url     : https://prove2.me/submissions/229d2a2d-d9ab-4777-8a73-8c5cae9e8694

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
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
theorem _root_.solution {x : K} (hx : x ≠ 0) : 0 ≤ v.ord x ↔ x ∈ v.ring := by
  rw [← v.valuation_le_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega
end GroundTheory.FunctionField.Place
