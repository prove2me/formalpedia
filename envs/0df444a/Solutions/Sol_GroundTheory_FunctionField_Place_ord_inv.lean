-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:08.440992+00:00
-- url     : https://prove2.me/submissions/5253c306-975f-45f6-bcae-f7b3ce5a7b4e

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
theorem _root_.solution (x : K) : v.ord x⁻¹ = -v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := v.ord_mul (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, ord_one] at h
  omega
end GroundTheory.FunctionField.Place
