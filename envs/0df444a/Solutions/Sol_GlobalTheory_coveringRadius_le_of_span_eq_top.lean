-- Prove2me | solution 1 for GlobalTheory.coveringRadius_le_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:23.151564+00:00
-- url     : https://prove2.me/submissions/12627397-00ac-4234-b4a4-9642596f9a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_mem_span
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
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → E} {r : ℝ}
    (hv : span ℝ (Set.range v) = ⊤) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) :
    coveringRadius L ≤ √(Fintype.card ι) / 2 * r :=
  coveringRadius_le fun x => by
    obtain ⟨w, hw, -, h⟩ := exists_mem_norm_sub_le_of_mem_span hL hr (x := x) (hv ▸ mem_top)
    exact ⟨w, hw, h⟩
end GlobalTheory
