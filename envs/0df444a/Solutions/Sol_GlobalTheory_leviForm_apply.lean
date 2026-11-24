-- Prove2me | solution 1 for GlobalTheory.leviForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:49.898069+00:00
-- url     : https://prove2.me/submissions/06ad5f9e-3d77-47e0-a5b7-77ce96843301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_fderiv_fderiv_ofReal_apply

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
variable {u u' : E → ℝ} {z : E}
namespace GlobalTheory
theorem _root_.solution (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    leviForm u z v w = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z v w
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • w) + I * fderiv ℝ (fderiv ℝ u) z v (I • w)
      - I * fderiv ℝ (fderiv ℝ u) z (I • v) w) := by
  rw [leviForm, ddbar_apply (contDiffAt_ofReal_comp hu)]
  simp only [fderiv_fderiv_ofReal_apply hu, smul_eq_mul]
end GlobalTheory
