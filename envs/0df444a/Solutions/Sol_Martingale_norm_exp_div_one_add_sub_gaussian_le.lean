-- Prove2me | solution 1 for Martingale.norm_exp_div_one_add_sub_gaussian_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:21:50.72175+00:00
-- url     : https://prove2.me/submissions/b79a1684-d4e0-4cf9-ab67-cad5ae6238a6

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option maxHeartbeats 1000000

theorem solution (x : ℝ) (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) / (1 + Complex.I * (x : ℂ))
        - ((Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ)‖ ≤ |x| ^ 3 := by
  set w : ℂ := ((Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ) with hw
  -- `‖1 + i x‖ ≥ 1`
  have hsq : ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ^ 2 = 1 + x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hge : (1:ℝ) ≤ ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ := by
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * (x : ℂ)), sq_nonneg x]
  have hle2 : ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ≤ 2 := by
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * (x : ℂ)), sq_abs x, abs_nonneg x]
  -- clear the denominator
  have hdiv : ‖Complex.exp (Complex.I * x) / (1 + Complex.I * (x : ℂ)) - w‖
      ≤ ‖Complex.exp (Complex.I * x) - (1 + Complex.I * (x : ℂ)) * w‖ := by
    have hzne : (1 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
      intro h; rw [h] at hge; simp at hge; linarith
    have hsplit : Complex.exp (Complex.I * x) / (1 + Complex.I * (x : ℂ)) - w
        = (Complex.exp (Complex.I * x) - (1 + Complex.I * (x : ℂ)) * w)
          / (1 + Complex.I * (x : ℂ)) := by field_simp
    rw [hsplit, norm_div, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (Complex.exp (Complex.I * x) - (1 + Complex.I * (x : ℂ)) * w)]
  refine le_trans hdiv ?_
  -- Taylor polynomial of order 3
  set T : ℂ := 1 + Complex.I * x - (x:ℂ)^2/2 - Complex.I * (x:ℂ)^3/6 with hT
  have hnormz : ‖Complex.I * (x : ℂ)‖ = |x| := by simp [Complex.norm_real]
  -- (a) `‖e^{ix} - T‖ ≤ (5/96)|x|⁴`
  have ha : ‖Complex.exp (Complex.I * (x:ℂ)) - T‖ ≤ |x| ^ 4 * (5 / 96) := by
    have h := Complex.exp_bound (x := Complex.I * (x : ℂ)) (by rw [hnormz]; exact hx)
      (n := 4) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 4, (Complex.I * (x:ℂ)) ^ i / (Nat.factorial i) = T := by
      simp [Finset.sum_range_succ, Nat.factorial, hT]
      ring_nf
      simp [Complex.I_sq, Complex.I_pow_three]
      ring
    rw [hsum, hnormz] at h
    refine le_trans h (le_of_eq ?_)
    norm_num [Nat.factorial]
  -- (b) `T - (1+ix)(1 - x²/2) = i x³/3`
  have hb : T - (1 + Complex.I * (x:ℂ)) * (1 - (x:ℂ)^2/2) = Complex.I * (x:ℂ)^3 / 3 := by
    rw [hT]; ring
  have hbn : ‖T - (1 + Complex.I * (x:ℂ)) * (1 - (x:ℂ)^2/2)‖ = |x| ^ 3 / 3 := by
    rw [hb]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_real, norm_pow]
  -- (c) `|1 - x²/2 - e^{-x²/2}| ≤ x⁴/4`
  have hc : ‖(1 - (x:ℂ)^2/2) - w‖ ≤ |x| ^ 4 / 4 := by
    have hreal : |Real.exp (-(x^2)/2) - 1 - (-(x^2)/2)| ≤ (-(x^2)/2) ^ 2 := by
      refine Real.abs_exp_sub_one_sub_id_le ?_
      rw [abs_le]
      constructor <;> nlinarith [sq_abs x, abs_nonneg x, sq_nonneg x]
    have heq : (1 - (x:ℂ)^2/2) - w = (((1 - x^2/2) - Real.exp (-(x^2)/2) : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    have : |(1 - x^2/2) - Real.exp (-(x^2)/2)| = |Real.exp (-(x^2)/2) - 1 - (-(x^2)/2)| := by
      rw [← abs_neg]; ring_nf
    rw [this]
    calc |Real.exp (-(x^2)/2) - 1 - (-(x^2)/2)| ≤ (-(x^2)/2) ^ 2 := hreal
      _ = |x| ^ 4 / 4 := by rw [← sq_abs x]; ring
  -- assemble
  have hsplit2 : Complex.exp (Complex.I * (x:ℂ)) - (1 + Complex.I * (x : ℂ)) * w
      = (Complex.exp (Complex.I * (x:ℂ)) - T)
        + (T - (1 + Complex.I * (x:ℂ)) * (1 - (x:ℂ)^2/2))
        + (1 + Complex.I * (x:ℂ)) * ((1 - (x:ℂ)^2/2) - w) := by ring
  have hx4 : |x| ^ 4 ≤ |x| ^ 3 := by
    have := abs_nonneg x
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  calc ‖Complex.exp (Complex.I * (x:ℂ)) - (1 + Complex.I * (x : ℂ)) * w‖
      ≤ ‖(Complex.exp (Complex.I * (x:ℂ)) - T)
          + (T - (1 + Complex.I * (x:ℂ)) * (1 - (x:ℂ)^2/2))‖
        + ‖(1 + Complex.I * (x:ℂ)) * ((1 - (x:ℂ)^2/2) - w)‖ := by
        rw [hsplit2]; exact norm_add_le _ _
    _ ≤ (‖Complex.exp (Complex.I * (x:ℂ)) - T‖
          + ‖T - (1 + Complex.I * (x:ℂ)) * (1 - (x:ℂ)^2/2)‖)
        + ‖(1 + Complex.I * (x:ℂ))‖ * ‖((1 - (x:ℂ)^2/2) - w)‖ := by
        gcongr
        · exact norm_add_le _ _
        · rw [norm_mul]
    _ ≤ (|x| ^ 4 * (5/96) + |x| ^ 3 / 3) + 2 * (|x| ^ 4 / 4) :=
        add_le_add (add_le_add ha (le_of_eq hbn))
          (mul_le_mul hle2 hc (norm_nonneg _) (by norm_num))
    _ ≤ |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3, pow_nonneg (abs_nonneg x) 4]
