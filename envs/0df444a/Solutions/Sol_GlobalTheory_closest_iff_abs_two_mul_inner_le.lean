-- Prove2me | solution 1 for GlobalTheory.closest_iff_abs_two_mul_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:22.307464+00:00
-- url     : https://prove2.me/submissions/e8ed9b86-10f9-4bbb-9a8c-68a273dad4a9

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
theorem _root_.solution {p w : E} (hw : w ∈ L) :
    (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ↔ ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  refine ⟨fun h y hy => abs_two_mul_inner_le_of_closest hw h hy, fun h z hz => ?_⟩
  have h1 := (abs_le.1 (h _ (sub_mem hz hw))).2
  have h2 := norm_sub_sq_real (p - w) (z - w)
  rw [sub_sub_sub_cancel_right] at h2
  exact (abs_le_of_sq_le_sq' (by linarith) (norm_nonneg _)).2
end GlobalTheory
