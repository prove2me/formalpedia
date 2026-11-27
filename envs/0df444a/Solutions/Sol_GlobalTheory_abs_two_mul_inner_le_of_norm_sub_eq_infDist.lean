-- Prove2me | solution 1 for GlobalTheory.abs_two_mul_inner_le_of_norm_sub_eq_infDist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:22.282267+00:00
-- url     : https://prove2.me/submissions/490ec515-e3ba-4ed2-873c-123f5bcfaa36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_abs_two_mul_inner_le_of_closest

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
theorem _root_.solution {p w : E} (hw : w ∈ L)
    (h : ‖p - w‖ = Metric.infDist p (L : Set E)) {y : E} (hy : y ∈ L) :
    |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 :=
  abs_two_mul_inner_le_of_closest hw (fun z hz => by
    rw [h, ← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hz) hy
end GlobalTheory
