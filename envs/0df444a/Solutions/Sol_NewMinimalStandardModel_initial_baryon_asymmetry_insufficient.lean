-- Prove2me | solution 1 for NewMinimalStandardModel.initial_baryon_asymmetry_insufficient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:50:43.743748+00:00
-- url     : https://prove2.me/submissions/4504da47-cf10-4b51-962b-f88b2bb51385

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

set_option autoImplicit false

theorem solution (N μF ρφ : ℝ)
    (hN : Real.log ((10 * 10 ^ 9 : ℝ) / (10 * 10 ^ 3)) ≤ N)
    (hμ : 0 < μF) (hρ : 0 < ρφ) (hdil : μF ^ 4 / ρφ = Real.exp (-4 * N)) :
    μF ^ 3 / ρφ ^ ((3 : ℝ) / 4) ≤ (10 : ℝ) ^ (-18 : ℤ) ∧
      μF ^ 3 / ρφ ^ ((3 : ℝ) / 4) < 88 / 10 ^ 12 := by
  have hρeq : ρφ = μF ^ 4 * Real.exp (4 * N) := by
    have h1 : μF ^ 4 = ρφ * Real.exp (-4 * N) := by
      rw [← hdil]; field_simp
    rw [h1, mul_assoc, ← Real.exp_add]; ring_nf; simp
  have hpow : ρφ ^ ((3 : ℝ) / 4) = μF ^ 3 * Real.exp (3 * N) := by
    rw [hρeq, Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul,
      ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
    norm_num
    left; ring
  have hx : μF ^ 3 / ρφ ^ ((3 : ℝ) / 4) = Real.exp (-3 * N) := by
    rw [hpow, div_mul_eq_div_div, div_self (pow_pos hμ 3).ne', one_div, ← Real.exp_neg]
    ring_nf
  have hL : Real.log ((10 * 10 ^ 9 : ℝ) / (10 * 10 ^ 3)) = Real.log ((10:ℝ) ^ 6) := by
    norm_num
  rw [hL] at hN
  have hle : Real.exp (-3 * N) ≤ (10 : ℝ) ^ (-18 : ℤ) := by
    have h1 : Real.exp (-3 * N) ≤ Real.exp (-3 * Real.log ((10:ℝ) ^ 6)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-3 * Real.log ((10:ℝ) ^ 6)) = (10 : ℝ) ^ (-18 : ℤ) := by
      rw [show -3 * Real.log ((10:ℝ) ^ 6) = -(((3:ℕ):ℝ) * Real.log ((10:ℝ) ^ 6)) by push_cast; ring,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity)]
      norm_num
    linarith
  rw [hx]
  refine ⟨hle, lt_of_le_of_lt hle ?_⟩
  norm_num
