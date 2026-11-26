-- Prove2me | solution 1 for MasulloRH.theta_norm_le_dyadic_on_tails
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:48:49.263461+00:00
-- url     : https://prove2.me/submissions/60d6ca76-bcbf-4b3d-ba29-510ae6e27d13

import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH.GaussianApproximation

theorem solution (x : ℝ) (hx : x ≤ -3 ∨ 3/2 ≤ x) :
    ‖theta x‖ ≤ 1/(2:ℝ)^64 := by
  let A (z : ℝ) := Real.pi * (Real.exp z)^2
  have he : (8/3 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  have hepow (n : ℕ) : (8/3 : ℝ)^n ≤ Real.exp (n : ℝ) := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he n).trans_eq
      (Real.exp_nat_mul 1 n).symm
  have hs : 24 * Real.exp (-54) ≤ 1/(2:ℝ)^64 := by
    have hc : 24 * (2:ℝ)^64 ≤ Real.exp 54 := (le_trans (by norm_num) (hepow 54))
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
    simpa using hc
  have gauss (z : ℝ) (hz : 1 ≤ A z) : ‖theta z‖ ≤ 24 * Real.exp (-A z) := by
    have ht := MasulloRH.theta_gaussian_truncation_error z 0
    norm_num only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add,
      one_pow, mul_zero, mul_one, sub_zero, neg_mul] at ht
    change ‖theta z‖ ≤ 12 * Real.exp (-A z) / (1 - Real.exp (-(A z*3))) at ht
    have hh : Real.exp (-(A z*3)) ≤ 1/2 := by
      calc Real.exp (-(A z*3)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
           _ = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
           _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
    apply ht.trans
    apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-(A z*3)))).2
    nlinarith [mul_nonneg (Real.exp_pos (-A z)).le
      (show 0 ≤ 1/2 - Real.exp (-(A z*3)) by linarith)]
  have sqexp (z : ℝ) : Real.exp (2*z) = (Real.exp z)^2 := by
    simpa using Real.exp_nat_mul z 2
  rcases hx with hx | hx
  · let y := -x - Real.log 4
    have hy : A y = Real.pi / 16 * Real.exp (-2*x) := by
      dsimp [A,y]
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<4),
        show -2*x = 2*(-x) by ring, sqexp]
      ring
    have h320 : 320 ≤ Real.exp 6 := le_trans (by norm_num) (hepow 6)
    have hlin : 320*(2*(-x-3)+1) ≤ Real.exp (-2*x) := by
      calc 320*(2*(-x-3)+1) ≤ Real.exp 6 * Real.exp (2*(-x-3)) :=
             mul_le_mul h320 (Real.add_one_le_exp _) (by linarith) (Real.exp_pos _).le
           _ = Real.exp (-2*x) := by rw [← Real.exp_add]; congr 1; ring
    have ha : -x + 54 ≤ A y := by
      rw [hy]
      calc -x + 54 ≤ 3/16*(320*(2*(-x-3)+1)) := by linarith
           _ ≤ Real.pi/16 * Real.exp (-2*x) := mul_le_mul
             (by linarith [Real.pi_gt_three] : (3:ℝ)/16 ≤ Real.pi/16)
             hlin (by linarith) (by positivity)
    have hg := gauss y (by linarith)
    rw [MasulloRH.theta_reflection x, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-x)/2 * ‖theta y‖ ≤ Real.exp (-x)/2 * (24 * Real.exp (-A y)) :=
           mul_le_mul_of_nonneg_left hg (by positivity)
         _ = 12 * Real.exp (-x + -A y) := by rw [Real.exp_add]; ring
         _ ≤ 12 * Real.exp (-54) := mul_le_mul_of_nonneg_left
           (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
         _ ≤ 24 * Real.exp (-54) := by linarith [Real.exp_pos (-54)]
         _ ≤ _ := hs
  · have hh : (8/3:ℝ)^3 ≤ Real.exp (2*x) := (hepow 3).trans
          (Real.exp_le_exp.mpr (by norm_num; linarith))
    have ha : 54 ≤ A x := by
      dsimp [A]
      rw [← sqexp]
      exact (show (54:ℝ) ≤ 3*(8/3)^3 by norm_num).trans
        (mul_le_mul Real.pi_gt_three.le hh (by norm_num) Real.pi_pos.le)
    exact (gauss x (by linarith)).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith : -A x ≤ -54)) (by norm_num)).trans hs)
