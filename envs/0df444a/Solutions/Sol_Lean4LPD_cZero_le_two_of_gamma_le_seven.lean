-- Prove2me | solution 1 for Lean4LPD.cZero_le_two_of_gamma_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:46.71764+00:00
-- url     : https://prove2.me/submissions/39091773-02dc-4983-956f-b6fd6bc5f669

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Theorems.Thm_Lean4LPD_root_factor_le
public import Theorems.Thm_Lean4LPD_exp_factor_le_sharp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG7 : G ≤ 7) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := id h
  have hrpos : (0 : ℝ) < r := by linarith
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hr32 : 32 / 7 ≤ r := by nlinarith only [hrG, hm2, hG7, hrpos]
  have hfrac : (r + 1) / r ≤ 39 / 32 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]
    linarith
  have hexp := exp_factor_le_sharp h hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have hchain : cZero r m G B ≤ 39 / 32 * (1439 / 1250) * Real.sqrt 2 := by
    unfold cZero
    exact mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [hchain, hs, Real.sqrt_nonneg 2]
end Lean4LPD
