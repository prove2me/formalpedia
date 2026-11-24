-- Prove2me | solution 1 for GlobalTheory.leviForm_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:36.295154+00:00
-- url     : https://prove2.me/submissions/30c2236e-e455-40e1-af4e-f52cb43cc51e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_ddbar_apply_self
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
theorem _root_.solution (hu : ContDiffAt ℝ 2 u z) (v : E) :
    leviForm u z v v = ((1 / 4 * (fderiv ℝ (fderiv ℝ u) z v v
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • v)) : ℝ) : ℂ) := by
  rw [leviForm, ddbar_apply_self (contDiffAt_ofReal_comp hu)]
  simp only [fderiv_fderiv_ofReal_apply hu, smul_eq_mul]
  push_cast; ring
end GlobalTheory
