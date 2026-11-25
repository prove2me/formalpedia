-- Prove2me | solution 1 for GlobalTheory.exists_mem_norm_sub_le_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:37.114197+00:00
-- url     : https://prove2.me/submissions/e53e082f-f2ed-40d8-aeed-2a3a23326057

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_span_int_norm_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → E} {r : ℝ}
    (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ L, w ∈ span ℝ (Set.range v) ∧ ‖x - w‖ ≤ √(Fintype.card ι) / 2 * r := by
  obtain ⟨w, hw, h⟩ := exists_mem_span_int_norm_sub_le v hr hx
  exact ⟨w, span_le.2 (Set.range_subset_iff.2 hL) hw, span_subset_span ℤ ℝ _ hw, h⟩
end GlobalTheory
