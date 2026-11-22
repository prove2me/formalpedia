-- Prove2me | solution 1 for Lean4LPD.cZero_le_ten_thirds_of_one_le_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:08.5018+00:00
-- url     : https://prove2.me/submissions/77a3aa24-d0fd-4d28-a160-efbbb371b353

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Theorems.Thm_Lean4LPD_exp_factor_le
public import Theorems.Thm_Lean4LPD_root_factor_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 10 / 3 := by
  obtain ⟨hr, hm, hG, _, _⟩ := id h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 2 := by rw [div_le_iff₀ hrpos]; linarith
  have hexp := exp_factor_le h hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have hchain : cZero r m G B ≤ 2 * (64 / 55) * Real.sqrt 2 := by
    unfold cZero
    exact mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [hchain, hs, Real.sqrt_nonneg 2]
end Lean4LPD
