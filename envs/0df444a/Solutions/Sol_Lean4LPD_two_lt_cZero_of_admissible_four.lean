-- Prove2me | solution 1 for Lean4LPD.two_lt_cZero_of_admissible_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:21.034986+00:00
-- url     : https://prove2.me/submissions/f34ef050-052c-43f7-8f39-c90b7c526881

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
theorem _root_.solution :
    Admissible 4 1 8 ∧ 2 < cZero 4 1 8 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) + 9 / 64 ≤ exp (9 / 4 * (1 + 1) / (4 * 8)) := by
    have := Real.add_one_le_exp (9 / 4 * (1 + 1) / (4 * 8) : ℝ)
    have harg : (9 : ℝ) / 4 * (1 + 1) / (4 * 8) = 9 / 64 := by norm_num
    rw [harg] at this
    linarith
  have hroot : (1.414 : ℝ) ≤ (1 + (1:ℝ)) ^ ((1 : ℝ) / (1 + 1)) := by
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
    have h3 : (1.414 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    calc (1.414 : ℝ) ≤ Real.sqrt 2 := h3
      _ = (2 : ℝ) ^ ((1 : ℝ) / 2) := h2.symm
      _ = (1 + (1:ℝ)) ^ ((1 : ℝ) / (1 + 1)) := by norm_num
  have hfrac : ((4:ℝ) + 1) / 4 = 5 / 4 := by norm_num
  have hexppos : (0 : ℝ) < exp (9 / 4 * (1 + 1) / (4 * 8)) := Real.exp_pos _
  unfold cZero
  rw [hfrac]
  nlinarith only [hexp, hroot, hexppos]
end Lean4LPD
