-- Prove2me | solution 1 for Lean4LPD.cZero_le_two_of_three_le_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:53.263138+00:00
-- url     : https://prove2.me/submissions/8c27fb57-96e5-4e62-b1e4-cd04a9a0edba

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Theorems.Thm_Lean4LPD_exp_le_one_div_one_sub

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm3 : 3 ≤ m)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  obtain ⟨hr, hm, hG, hmr, hrG⟩ := h
  have hr3 : (3 : ℝ) ≤ r := le_trans hm3 hmr
  have hrpos : (0 : ℝ) < r := by linarith
  have hm4 : (4 : ℝ) ≤ m + 1 := by linarith
  have hfrac : (r + 1) / r ≤ 4 / 3 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]; linarith
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hexp : exp (9 / 4 * (m + 1) / (r * G)) ≤ 128 / 119 := by
    have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 128 := by
      rw [div_le_iff₀ hrGpos]; nlinarith only [hrG, hm4]
    calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 128) := Real.exp_le_exp.mpr hkey
      _ ≤ 1 / (1 - 9 / 128) := exp_le_one_div_one_sub (by norm_num)
      _ = 128 / 119 := by norm_num
  have hquart : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 1.2 := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
    have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4]; norm_num
  have hroot : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ 1.2 := by
    have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (2 : ℝ) ^ ((1 : ℝ) / (m + 1)) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / (m + 1)) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  unfold cZero
  have := mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [this]
end Lean4LPD
