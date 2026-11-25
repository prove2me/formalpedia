-- Prove2me | solution 1 for GlobalTheory.exists_mem_norm_sub_le_lastMin_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:53.792989+00:00
-- url     : https://prove2.me/submissions/5d4d0357-5650-49a6-8c1d-1373e845c49d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_mem_span
import Theorems.Thm_GlobalTheory_exists_linearIndependent_norm_le_succMin
import Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int


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
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] {x : E} (hx : x ∈ span ℝ (L : Set E)) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℤ L) / 2 * lastMin L := by
  obtain ⟨v, hv, h⟩ := exists_linearIndependent_norm_le_succMin (L := L) le_rfl
  have hs : span ℝ (Set.range v) = span ℝ (L : Set E) :=
    eq_of_le_of_finrank_eq (span_mono (Set.range_subset_iff.2 fun i => (h i).1))
      (by rw [finrank_span_eq_card hv, Fintype.card_fin])
  obtain ⟨w, hw, -, h'⟩ := exists_mem_norm_sub_le_of_mem_span (fun i => (h i).1)
    (fun i => (h i).2) (x := x) (by rwa [hs])
  refine ⟨w, hw, ?_⟩
  rwa [Fintype.card_fin, ← lastMin, finrank_span_eq_finrank_int] at h'
end GlobalTheory
