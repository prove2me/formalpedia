-- Prove2me | solution 1 for GlobalTheory.leviForm_log_normSq_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:25.241261+00:00
-- url     : https://prove2.me/submissions/342391d2-33a1-46d7-a46a-e2ddbefd18d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_leviForm_comp_holo

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]
variable {φ : E → H} {z : E}
namespace GlobalTheory
theorem _root_.solution {δ : ℝ} (hφ : ContDiffAt ℂ 2 φ z)
    (hz : ‖φ z‖ ^ 2 + δ ≠ 0) (v w : E) :
    leviForm (fun x => Real.log (‖φ x‖ ^ 2 + δ)) z v w =
      inner ℂ (fderiv ℂ φ z w) (fderiv ℂ φ z v) / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ)
        - inner ℂ (φ z) (fderiv ℂ φ z v) * inner ℂ (fderiv ℂ φ z w) (φ z)
          / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ) ^ 2 := by
  rw [leviForm_comp_holo (u := fun y : H => Real.log (‖y‖ ^ 2 + δ))
    (((contDiff_norm_sq ℂ).contDiffAt.add contDiffAt_const).log hz) hφ,
    leviForm_log_normSq_add hz]
end GlobalTheory
