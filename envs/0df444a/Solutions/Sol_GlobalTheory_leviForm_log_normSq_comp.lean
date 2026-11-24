-- Prove2me | solution 1 for GlobalTheory.leviForm_log_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:04.371069+00:00
-- url     : https://prove2.me/submissions/6ec8cae0-d93d-4947-8f85-1a6c53927e31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_leviForm_log_normSq_add_comp

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
theorem _root_.solution (hφ : ContDiffAt ℂ 2 φ z) (hz : φ z ≠ 0) (v w : E) :
    leviForm (fun x => Real.log (‖φ x‖ ^ 2)) z v w =
      inner ℂ (fderiv ℂ φ z w) (fderiv ℂ φ z v) / (‖φ z‖ : ℂ) ^ 2
        - inner ℂ (φ z) (fderiv ℂ φ z v) * inner ℂ (fderiv ℂ φ z w) (φ z) / (‖φ z‖ : ℂ) ^ 4 := by
  have := leviForm_log_normSq_add_comp (δ := 0) hφ (by simpa using hz) v w
  simp only [add_zero] at this
  rw [this]; push_cast; ring
end GlobalTheory
