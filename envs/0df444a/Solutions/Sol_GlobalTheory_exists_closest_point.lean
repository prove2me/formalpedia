-- Prove2me | solution 1 for GlobalTheory.exists_closest_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:31.474139+00:00
-- url     : https://prove2.me/submissions/47dc4028-7ac7-4e6b-af7b-7722a503424e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_norm_sub_eq_infDist


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
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L] (x : F) :
    ∃ w ∈ L, ∀ z ∈ L, ‖x - w‖ ≤ ‖x - z‖ := by
  obtain ⟨w, hw, h⟩ := exists_norm_sub_eq_infDist L x
  refine ⟨w, hw, fun z hz => ?_⟩
  rw [h, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hz
end GlobalTheory
