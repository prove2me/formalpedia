-- Prove2me | solution 1 for GlobalTheory.exists_closest_point_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:34.642211+00:00
-- url     : https://prove2.me/submissions/fffa7776-aa77-4b10-9f2e-20a93dfc50e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_closest_point
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
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (p : E) :
    ∃ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) ∧ ‖p - w‖ ≤ ‖p‖ ∧
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  obtain ⟨w, hw, h⟩ := exists_closest_point L p
  exact ⟨w, hw, h, by simpa using h 0 L.zero_mem,
    fun y hy => abs_two_mul_inner_le_of_closest hw h hy⟩
end GlobalTheory
