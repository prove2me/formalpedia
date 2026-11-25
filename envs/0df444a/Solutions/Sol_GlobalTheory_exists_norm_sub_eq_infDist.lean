-- Prove2me | solution 1 for GlobalTheory.exists_norm_sub_eq_infDist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:59.21849+00:00
-- url     : https://prove2.me/submissions/6d975184-d15d-4c36-ba74-7ec517a9fa75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

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
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E) : ∃ w ∈ L, ‖x - w‖ = Metric.infDist x (L : Set E) := by
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hc : IsClosed (L.toAddSubgroup : Set E) := inferInstance
  obtain ⟨w, hw, h⟩ := hc.exists_infDist_eq_dist ⟨0, L.zero_mem⟩ x
  exact ⟨w, hw, by rw [← dist_eq_norm]; exact h.symm⟩
end GlobalTheory
