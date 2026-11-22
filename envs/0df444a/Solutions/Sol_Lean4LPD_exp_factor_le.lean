-- Prove2me | solution 1 for Lean4LPD.exp_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:00:27.7178+00:00
-- url     : https://prove2.me/submissions/a1f37cb9-c658-4753-a21d-b250f2e59652

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
theorem _root_.solution {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 64 / 55 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 64 := by
    rw [div_le_iff₀ hrGpos]
    nlinarith only [hrG, hm2]
  calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 64) := Real.exp_le_exp.mpr hkey
    _ ≤ 1 / (1 - 9 / 64) := exp_le_one_div_one_sub (by norm_num)
    _ = 64 / 55 := by norm_num
end Lean4LPD
