-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.exists_not_mem_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:17.949369+00:00
-- url     : https://prove2.me/submissions/b0e19eee-fa7f-44be-9484-0d52852d08a1

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, x ∉ v.ring := by
  have hx' : Transcendental k x⁻¹ := fun h => hx (by simpa using IsAlgebraic.inv_iff.2 h)
  obtain ⟨v, hv⟩ := exists_valuation_lt_one_of_transcendental hx'
  refine ⟨v, fun hmem => ?_⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have h1 := (v.ring.valuation_le_one_iff x).2 hmem
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at hv
  exact absurd h1 (not_le.2 hv)
end GroundTheory.FunctionField.Place
