-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:59.605295+00:00
-- url     : https://prove2.me/submissions/a640a861-7103-4aa8-b9e9-2fc9ab77f066

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_inv

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
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v.ord (x / y) = v.ord x - v.ord y := by
  rw [div_eq_mul_inv, v.ord_mul hx (inv_ne_zero hy), ord_inv]
  ring
end GroundTheory.FunctionField.Place
