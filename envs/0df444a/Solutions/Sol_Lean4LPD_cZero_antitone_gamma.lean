-- Prove2me | solution 1 for Lean4LPD.cZero_antitone_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:44.492575+00:00
-- url     : https://prove2.me/submissions/262a97b1-f4fa-4e2e-a7dc-83c53749bb15

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
theorem _root_.solution {r m B G G' : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hG : 0 < G) (hGG' : G ≤ G') : cZero r m G' B ≤ cZero r m G B := by
  have hrG : 0 < r * G := mul_pos hr hG
  have hrG' : 0 < r * G' := mul_pos hr (lt_of_lt_of_le hG hGG')
  have hnum : (0 : ℝ) ≤ 9 / 4 * (m + 1) := by linarith
  have harg : 9 / 4 * (m + 1) / (r * G') ≤ 9 / 4 * (m + 1) / (r * G) := by
    apply div_le_div_of_nonneg_left hnum hrG
    exact mul_le_mul_of_nonneg_left hGG' hr.le
  have hexp := Real.exp_le_exp.mpr harg
  have hfrac : (0 : ℝ) ≤ (r + 1) / r := by positivity
  have hroot : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) :=
    Real.rpow_nonneg (by linarith) _
  unfold cZero
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hfrac) hroot
end Lean4LPD
