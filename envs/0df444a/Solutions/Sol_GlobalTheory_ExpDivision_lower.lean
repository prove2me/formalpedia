-- Prove2me | solution 1 for GlobalTheory.ExpDivision.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:21.819684+00:00
-- url     : https://prove2.me/submissions/cc66c371-b782-4038-b1a2-a4df6712a44d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_mul_quot
import Theorems.Thm_GlobalTheory_ExpDivision_quot_zero
import Theorems.Thm_GlobalTheory_ExpDivision_norm_exp_sub_one_ge
import Theorems.Thm_GlobalTheory_ExpDivision_dioph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (t : ℝ) :
    1 ≤ 2 * (1 + |t|) ^ 2 * (‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖) := by
  have a0 := abs_nonneg t
  have n1 := norm_nonneg (quot (2 * Real.pi) t)
  have n2 := norm_nonneg (quot (2 * Real.pi * √2) t)
  have e1 : 4 * |t - round t| ≤ |t| * ‖quot (2 * Real.pi) t‖ := by
    have := norm_exp_sub_one_ge t
    rwa [Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
  have e2 : 4 * |√2 * t - round (√2 * t)| ≤ |t| * ‖quot (2 * Real.pi * √2) t‖ := by
    have := norm_exp_sub_one_ge (√2 * t)
    rwa [← mul_assoc, Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at this
  by_cases hp : round t = 0
  · have h1 : 1 ≤ ‖quot (2 * Real.pi) t‖ := by
      by_cases ht : t = 0
      · subst ht
        rw [Complex.ofReal_zero, quot_zero, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [Real.pi_gt_three]
      · rw [hp] at e1
        simp only [Int.cast_zero, sub_zero] at e1
        have : 0 < |t| := abs_pos.2 ht
        by_contra hh
        nlinarith
    have h2 : 1 ≤ (1 + |t|) ^ 2 := by nlinarith
    nlinarith
  · have h := dioph t hp
    set s := ‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖ with hs
    have hs0 : 0 ≤ s := by positivity
    have h1 : 4 * (|t - round t| + |√2 * t - round (√2 * t)|) ≤ (1 + |t|) * s := by
      rw [hs]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + |t| by positivity)
    have h3 : 0 ≤ (1 + |t|) ^ 2 * s := by positivity
    nlinarith
end GlobalTheory.ExpDivision
