-- Prove2me | solution 1 for GlobalTheory.exists_mem_span_int_norm_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:27.840731+00:00
-- url     : https://prove2.me/submissions/4d1eb9c4-c415-4833-866b-c257528a0457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_int_comb_norm_sub_sq_le

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
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (v : ι → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  let e := (Fintype.equivFin ι).symm
  have hr : Set.range (v ∘ e) = Set.range v := e.surjective.range_comp v
  obtain ⟨w, hw, h⟩ := exists_int_comb_norm_sub_sq_le _ (v ∘ e) (x := x) (by rwa [hr])
  refine ⟨w, by rwa [hr] at hw, h.trans_eq ?_⟩
  congr 1
  exact e.sum_comp (fun i => ‖v i‖ ^ 2)
end GlobalTheory
