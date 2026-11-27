-- Prove2me | solution 1 for MasulloRH.quarter_shift_conjugate_test_zero_free_through_twenty_seven_fourths
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:19:21.289797+00:00
-- url     : https://prove2.me/submissions/599606d8-c278-452d-9951-646056a54b47

import Theorems.Thm_MasulloRH_real_residual_conjugate_frequency_gain
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_zero_free_rectangle
import Theorems.Thm_MasulloRH_twenty_five_rational_translates_gaussian_all_windows
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_exterior_energy
import Theorems.Thm_MasulloRH_fixed_gaussian_residual_laplace_at_zeta_zero
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory MasulloRH MasulloRH.WindowLaplaceGram MasulloRH.GaussianApproximation
open MasulloRH.ThetaDerivativeCertificate MasulloRH.CentralInterval
open scoped ComplexConjugate

theorem solution (s : ℂ) (hl : 9/16 ≤ s.re) (hr : s.re ≤ 15/16) (hi : |s.im| ≤ 27/4) :
    riemannZeta s ≠ 0 := by
  by_cases low : |s.im| ≤ 133/20
  · exact MasulloRH.quarter_shift_gaussian_zero_free_rectangle s hl hr low
  have height_gt := lt_of_not_ge low
  intro hz
  have hm := MasulloRH.fixed_gaussian_residual_laplace_at_zeta_zero
    (fun i : Fin 25 => (coeff i:ℂ)) (fun i => (shift i:ℝ)) s (by linarith) (by linarith) hz
  have he := (MasulloRH.quarter_shift_gaussian_exterior_energy (3/4) (1/4) (by norm_num) (by norm_num)).1
  have hE := MasulloRH.twenty_five_rational_translates_gaussian_all_windows.1 (3/4) (1/4)
    (by norm_num) (by norm_num)
  have hreal (x : ℝ) : conj (err x) = err x := by
    have thetaReal (u : ℝ) : conj (theta u)=theta u := by
      simp only [theta,Complex.conj_tsum,Complex.conj_ofReal]
    have pulseReal : conj (pulse 0 x)=pulse 0 x := by simp [pulse,←Complex.exp_conj]
    simp [err,GaussianApproximation.residual,thetaReal,pulseReal]
  have pair := MasulloRH.real_residual_conjugate_frequency_gain (3/4) (1/4) err s
    (abs_lt.mpr ⟨by linarith,by linarith⟩) (by linarith) hreal he hm.1
  have val : moment err s = Complex.exp (s^2/4) := hm.2
  have vnorm : ‖Complex.exp (s^2/4)‖^2 = Real.exp ((s.re^2-s.im^2)/2) := by
    rw [Complex.norm_exp,←Real.exp_nat_mul]
    congr 1
    norm_num [pow_two,Complex.div_re,Complex.mul_re]
    ring
  rw [val,vnorm] at pair
  have hnum : (1/6800000000:ℚ) ≤ (expPoint (-11583/512)).1 := by decide +kernel
  have hbox := (MasulloRH.central_interval_arithmetic_sound.exp_ok
    (MasulloRH.central_interval_arithmetic_sound.point_ok (-11583/512))).1
  have hlo : ((expPoint (-11583/512)).1:ℝ) ≤ Real.exp (-11583/512) := by
    simpa only [expB,point,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] using hbox
  have hx : (1/6800000000:ℝ) ≤ Real.exp ((s.re^2-s.im^2)/2) := by
    have ht : s.im^2 ≤ (27/4:ℝ)^2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
    have hσ := pow_le_pow_left₀ (by norm_num : 0≤(9/16:ℝ)) hl 2
    have cast := (Rat.cast_le (K:=ℝ)).mpr hnum
    rw [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at cast
    exact cast.trans (hlo.trans (Real.exp_le_exp.mpr (by linarith only [ht,hσ])))
  have hpos : 0 < s.re-1/2 := by linarith
  have hpos' : 0 < 1-s.re := by linarith
  have ww : 1/(2*(s.re-((3/4:ℝ)-1/4)))+1/(2*(3/4+1/4-s.re)) ≤ 64/7 := by
    have hpoly := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
    have ident : 1/(2*(s.re-1/2))+1/(2*(1-s.re)) = (1/4)/((s.re-1/2)*(1-s.re)) := by
      have aa : 2*(s.re-1/2) ≠ 0 := mul_ne_zero (by norm_num) hpos.ne'
      have bb : 2*(1-s.re) ≠ 0 := mul_ne_zero (by norm_num) hpos'.ne'
      rw [div_add_div _ _ aa bb]
      apply (div_eq_div_iff (mul_ne_zero aa bb) (mul_ne_zero hpos.ne' hpos'.ne')).2
      ring
    rw [show (3/4:ℝ)-1/4=1/2 by norm_num,show (3/4:ℝ)+1/4=1 by norm_num]
    rw [ident,div_le_iff₀ (mul_pos hpos hpos')]
    nlinarith only [hpoly]
  have it : 1/|s.im| ≤ 1/6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have cap := mul_le_mul (le_of_lt hE) (add_le_add ww it) (by
    have a : 0 < s.re-(3/4-1/4) := by linarith
    have b : 0 < 3/4+1/4-s.re := by linarith
    positivity) (by norm_num)
  linarith only [hx,pair,cap]
