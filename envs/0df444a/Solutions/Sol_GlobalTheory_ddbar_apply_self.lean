-- Prove2me | solution 1 for GlobalTheory.ddbar_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:57.790509+00:00
-- url     : https://prove2.me/submissions/a217876d-41b3-40ec-b77f-7df65cc91288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {u u' : E → F} {z : E}
namespace GlobalTheory
theorem _root_.solution (hu : ContDiffAt ℝ 2 u z) (v : E) :
    ddbar u z v v = (1 / 4 : ℂ) • (fderiv ℝ (fderiv ℝ u) z v v
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • v)) := by
  rw [ddbar_apply hu, (hu.isSymmSndFDerivAt (by simp)).eq v (I • v), add_sub_cancel_right]
end GlobalTheory
