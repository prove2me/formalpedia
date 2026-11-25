-- Prove2me | solution 1 for GlobalTheory.coveringRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:52:12.481918+00:00
-- url     : https://prove2.me/submissions/788c4c9e-6443-440a-a0e8-3e7053ea1bc8

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
theorem _root_.solution (h : ∀ x : E, ∃ w ∈ L, ‖x - w‖ ≤ r) : coveringRadius L ≤ r :=
  ciSup_le fun x => by
    obtain ⟨w, hw, h⟩ := h x
    exact (Metric.infDist_le_dist_of_mem hw).trans (by rwa [dist_eq_norm])
end GlobalTheory
