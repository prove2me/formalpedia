-- Prove2me | solution 1 for Lean4LPD.cZero_le_two_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:03:25.424827+00:00
-- url     : https://prove2.me/submissions/47c3736e-8e0d-48e3-a65b-645dd8fea1fd

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
theorem _root_.solution {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 384 / 275 * Real.sqrt 2 := by
  obtain ⟨hr, hm, hG, hmr, hrG⟩ := h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 6 / 5 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]
    linarith
  have hexp := exp_factor_le (r := r) (m := m) (G := G) ⟨hr, hm, hG, hmr, hrG⟩ hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / (m + 1)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hsqrt : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc cZero r m G B
      = (r + 1) / r * exp (9 / 4 * (m + 1) / (r * G)) * (1 + B) ^ ((1 : ℝ) / (m + 1)) := rfl
    _ ≤ (6 / 5) * (64 / 55) * Real.sqrt 2 := by
        apply mul_le_mul (mul_le_mul hfrac hexp (le_of_lt hexppos) (by norm_num)) hroot
          (le_of_lt hrootpos) (by positivity)
    _ = 384 / 275 * Real.sqrt 2 := by ring
end Lean4LPD
