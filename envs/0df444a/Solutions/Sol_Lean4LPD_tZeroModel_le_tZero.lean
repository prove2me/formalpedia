-- Prove2me | solution 1 for Lean4LPD.tZeroModel_le_tZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:59.200656+00:00
-- url     : https://prove2.me/submissions/5471c248-1f23-41cc-a7ce-0d4fc6c5237c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Theorems.Thm_Lean4LPD_cZero_le_two


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {r m G B kh a : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a) :
    tZeroModel G kh a ≤ tZero (cZero r m G B) G kh a := by
  obtain ⟨_, _, hG, _, _⟩ := id h
  have hkh1 : (0 : ℝ) < kh - 1 := by linarith
  have hc2 : cZero r m G B ≤ 2 := cZero_le_two h hm1 hr5 hB0 hB1
  have hcpos : 0 < cZero r m G B := by
    unfold cZero
    obtain ⟨hr', _, _, _, _⟩ := id h
    have hrpos : (0 : ℝ) < r := by linarith
    have h1 : (0 : ℝ) < (r + 1) / r := div_pos (by linarith) hrpos
    have h2 : (0 : ℝ) < Real.exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
    have h3 : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hden : 0 < cZero r m G B * G * (kh - 1) * a := by positivity
  unfold tZeroModel tZero
  apply one_div_le_one_div_of_le hden
  nlinarith [hc2, hG.le, hkh1.le, ha.le, mul_pos hG hkh1]
end Lean4LPD
