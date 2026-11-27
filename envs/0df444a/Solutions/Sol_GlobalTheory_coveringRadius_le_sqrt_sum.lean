-- Prove2me | solution 1 for GlobalTheory.coveringRadius_le_sqrt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:27.111788+00:00
-- url     : https://prove2.me/submissions/c7f655f9-287d-4e1c-b2c2-47f532f2d055

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_sq_le_of_mem_span
import Theorems.Thm_GlobalTheory_coveringRadius_le


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
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) :
    coveringRadius L ≤ √(∑ i, ‖v i‖ ^ 2) / 2 :=
  coveringRadius_le fun x => by
    obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_sq_le_of_mem_span hL (x := x) (hv ▸ mem_top)
    refine ⟨w, hw, (abs_le_of_sq_le_sq' ?_ (by positivity)).2⟩
    rw [div_pow, Real.sq_sqrt (by positivity)]
    linarith
end GlobalTheory
