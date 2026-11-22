-- Prove2me | solution 1 for Lean4LPD.cZero_le_four_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:56.565626+00:00
-- url     : https://prove2.me/submissions/80812af0-230d-49d7-91b9-0f49b876b4c8

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    cZero r m G B ≤ 4 * exp (9 / 32) := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 2 := by rw [div_le_iff₀ hrpos]; linarith
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 32 := by
    rw [div_le_iff₀ hrGpos]; nlinarith only [hrG, hm]
  have hexp : exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 32) := Real.exp_le_exp.mpr hkey
  have hroot : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ 2 := by
    have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (1 + B) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      rw [div_le_one (by linarith)]; linarith
    rw [Real.rpow_one] at h1; linarith
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hEpos : (0 : ℝ) < exp (9 / 32) := Real.exp_pos _
  unfold cZero
  have := mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos
    (by positivity)
  nlinarith only [this, hEpos]
end Lean4LPD
