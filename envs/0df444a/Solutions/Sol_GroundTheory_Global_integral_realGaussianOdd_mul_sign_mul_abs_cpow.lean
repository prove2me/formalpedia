-- Prove2me | solution 1 for GroundTheory.Global.integral_realGaussianOdd_mul_sign_mul_abs_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:45.914901+00:00
-- url     : https://prove2.me/submissions/7f6a6488-249d-41a9-ae1c-4af19de798b0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Theorems.Thm_GroundTheory_Global_realGaussian_eq_ofReal
import Theorems.Thm_GroundTheory_Global_integral_comp_abs_complex
import Theorems.Thm_GroundTheory_Global_mellin_exp_neg_pi_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution {s : ℂ} (hs : -1 < s.re) :
    ∫ x : ℝ, realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) =
      Gammaℝ (s + 1) := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have h : (fun x : ℝ ↦ realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s /
        ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s /
        (y : ℂ)) |x| := by
    funext x
    have hx : (x : ℂ) * (Real.sign x : ℂ) = ((|x| : ℝ) : ℂ) := by
      rw [← ofReal_mul]
      congr 1
      rcases lt_trichotomy x 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · simp [h]
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    rw [realGaussianOdd, ← realGaussian, realGaussian_eq_ofReal]
    simp only [sq_abs]
    rw [← hx]
    ring
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)
      = mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) (s + 1) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    rw [add_sub_cancel_right, smul_eq_mul]
    field_simp
  rw [this, mellin_exp_neg_pi_mul_sq hs1]
  ring
end GroundTheory.Global
