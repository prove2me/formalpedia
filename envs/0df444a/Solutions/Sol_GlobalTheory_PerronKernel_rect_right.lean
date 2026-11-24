-- Prove2me | solution 1 for GlobalTheory.PerronKernel.rect_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:36.556183+00:00
-- url     : https://prove2.me/submissions/8b65d8dc-e1a8-4d17-abc7-d2d8b45308f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution (L : ℝ) {a b : ℝ} (T : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    + I * (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
    - I * (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I)) = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => cexp (L * z) / z)
      (Set.uIcc ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re ((b : ℂ) + T * I).re ×ℂ
        Set.uIcc ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im ((b : ℂ) + T * I).im) := by
    rintro z ⟨hzr, -⟩
    have hre : a ≤ z.re := by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
        add_zero] at hzr
      rcases Set.mem_uIcc.mp hzr with h | h <;> linarith [h.1, h.2]
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div (by fun_prop) differentiableAt_id
    intro h0
    rw [h0, zero_re] at hre
    linarith
  have h1 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re = a := by simp
  have h2 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have h3 : ((b : ℂ) + (T : ℂ) * I).re = b := by simp
  have h4 : ((b : ℂ) + (T : ℂ) * I).im = T := by simp
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z : ℂ => cexp (L * z) / z) ((a : ℂ) + ((-T : ℝ) : ℂ) * I) ((b : ℂ) + T * I) hd
  rw [h1, h2, h3, h4] at this
  simpa only [smul_eq_mul] using this
end GlobalTheory.PerronKernel
