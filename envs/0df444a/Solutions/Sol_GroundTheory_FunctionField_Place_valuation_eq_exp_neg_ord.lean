-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_eq_exp_neg_ord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:05.905842+00:00
-- url     : https://prove2.me/submissions/5755a3d0-7ec7-4df5-b2c7-233bc5af684f

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs

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
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    v.valuation x = WithZero.exp (-v.ord x) := by
  rw [ord, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]
end GroundTheory.FunctionField.Place
