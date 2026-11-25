-- Prove2me | solution 1 for GlobalTheory.exists_mem_norm_sub_le_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:52.515157+00:00
-- url     : https://prove2.me/submissions/824da709-bb1d-4ae3-89d1-a4c6f53617e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_mem_span

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
theorem _root_.solution [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {v : ι → E} {r : ℝ} (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι = finrank ℝ E) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r := by
  have hs : span ℝ (Set.range v) = ⊤ :=
    eq_top_of_finrank_eq (by rw [finrank_span_eq_card hv, hn])
  obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_le_of_mem_span hL hr (x := x) (hs ▸ mem_top)
  exact ⟨w, hw, hn ▸ h⟩
end GlobalTheory
