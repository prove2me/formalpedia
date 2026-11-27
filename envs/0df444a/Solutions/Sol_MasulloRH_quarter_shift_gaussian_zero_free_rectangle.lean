-- Prove2me | solution 1 for MasulloRH.quarter_shift_gaussian_zero_free_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:18:48.365353+00:00
-- url     : https://prove2.me/submissions/d7f5fe45-f23b-4c28-a721-e6ae7b336224

import Theorems.Thm_MasulloRH_quarter_shift_zeta_zero_height_profile
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.Tactic.Linarith

open MasulloRH MasulloRH.CentralInterval

theorem solution (s : ℂ) (hl : 9/16 ≤ s.re) (hr : s.re ≤ 15/16) (hi : |s.im| ≤ 133/20) :
    riemannZeta s ≠ 0 := by
  intro hz
  have zero := quarter_shift_zeta_zero_height_profile s (by linarith) (by linarith) hz
  have ht : s.im^2 ≤ (133/20:ℝ)^2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hu : (9/16:ℝ)^2 ≤ s.re^2 := pow_le_pow_left₀ (by norm_num) hl 2
  have hnum : (1/3490000000:ℚ) ≤ (expPoint (-703/32)).1 := by decide +kernel
  have hx : (1/3490000000:ℝ) ≤ Real.exp ((s.re^2-s.im^2)/2) := by
    have hh := (MasulloRH.central_interval_arithmetic_sound.exp_ok
      (MasulloRH.central_interval_arithmetic_sound.point_ok (-703/32))).1
    have hlow : ((expPoint (-703/32)).1:ℝ) ≤ Real.exp (-703/32) := by
      simpa only [expB,point,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] using hh
    have hcast := (Rat.cast_le (K:=ℝ)).mpr hnum
    rw [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hcast
    exact hcast.trans (hlow.trans (Real.exp_le_exp.mpr (by linarith only [hu,ht])))
  have hpol : (7/64:ℝ) ≤ 4*(s.re-1/2)*(1-s.re) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)]
  have hfinal := mul_le_mul hx hpol (by norm_num) (Real.exp_pos _).le
  linarith only [hfinal,zero]
