-- Prove2me | solution 1 for MasulloRH.nine_shift_gaussian_zero_free_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:51:27.923451+00:00
-- url     : https://prove2.me/submissions/bbd1f62d-dd85-4e2f-bfd3-bf97f5e73f79

import Theorems.Thm_MasulloRH_nine_rational_theta_shifts_on_every_gaussian_window
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

open MasulloRH MasulloRH.NineShift MasulloRH.GaussianApproximation

theorem solution (s : ℂ) (hl : 9/16 ≤ s.re) (hr : s.re ≤ 15/16) (hi : |s.im| ≤ 3) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hd : |s.re-(3/4)| ≤ 3/16 := abs_le.mpr ⟨by linarith,by linarith⟩
  have ho := MasulloRH.fixed_gaussian_energy_lower_at_every_zeta_zero (3/4) (15/64)
    (by norm_num) (by norm_num) (fun i : Fin 9 => (coeff i:ℂ)) (fun i => (shift i:ℝ)) s
    (hd.trans_lt (by norm_num)) hz
  change _ ≤ energy (3/4) (15/64) err at ho
  have hw := MasulloRH.nine_rational_theta_shifts_on_every_gaussian_window.1
    (3/4) (15/64) (by norm_num) (by norm_num)
  have hd2 : (s.re-3/4)^2 ≤ (3/16:ℝ)^2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hi2 : s.im^2 ≤ (3:ℝ)^2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
  have he5 : Real.exp 5 ≤ (3:ℝ)^5 := by
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using
      (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5)
  have hfac : (1/243:ℝ) ≤ Real.exp ((s.re^2-s.im^2)/2) := by
    calc _ ≤ 1/Real.exp 5 := one_div_le_one_div_of_le (Real.exp_pos _) (by linarith only [he5])
         _ = Real.exp (-5) := by rw [Real.exp_neg,one_div]
         _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hi2,sq_nonneg s.re])
  have hpol : (27/320:ℝ) ≤ ((15/64:ℝ)^2-(s.re-3/4)^2)/(15/64) := by linarith only [hd2]
  have hp := mul_le_mul hfac hpol (by norm_num) (Real.exp_pos _).le
  linarith only [hp,ho,hw]
