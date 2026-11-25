-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_eq_one_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:10.116322+00:00
-- url     : https://prove2.me/submissions/bdfb16a9-b65c-4b50-82a8-61c778ea0492

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (v : Place k K) {x : K} (hx : IsAlgebraic k x)
    (hx0 : x ≠ 0) : v.ring.valuation x = 1 := by
  have h1 := (v.ring.valuation_le_one_iff x).2 (v.mem_ring_of_isAlgebraic hx)
  have h2 := (v.ring.valuation_le_one_iff x⁻¹).2
    (v.mem_ring_of_isAlgebraic (IsAlgebraic.inv_iff.2 hx))
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at h2
  exact le_antisymm h1 h2
end GroundTheory.FunctionField.Place
