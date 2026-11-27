-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.min_le_ord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:47.277092+00:00
-- url     : https://prove2.me/submissions/86255e2d-153c-40e5-8b6c-4618da39136e

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
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
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by
  have h := Valuation.map_add v.valuation x y
  rw [v.valuation_eq_exp_neg_ord hx, v.valuation_eq_exp_neg_ord hy,
    v.valuation_eq_exp_neg_ord hxy, le_max_iff, WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  omega
end GroundTheory.FunctionField.Place
