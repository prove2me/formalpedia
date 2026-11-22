-- Prove2me | solution 1 for Lean4LPD.cZero_extremal_isotone_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:52.76896+00:00
-- url     : https://prove2.me/submissions/6f010e20-c94b-45d4-a703-389a92466ddb

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
    Admissible (32 / 6) 1 6 ∧ Admissible (32 / 7) 1 7 ∧
      cZero (32 / 6) 1 6 1 < cZero (32 / 7) 1 7 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have h6 : (9 : ℝ) / 4 * (1 + 1) / (32 / 6 * 6) = 9 / 64 := by norm_num
  have h7 : (9 : ℝ) / 4 * (1 + 1) / (32 / 7 * 7) = 9 / 64 := by norm_num
  have hE : (0 : ℝ) < exp (9 / 64) := Real.exp_pos _
  have hR : (0 : ℝ) < (1 + (1 : ℝ)) ^ ((1 : ℝ) / (1 + 1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold cZero
  rw [h6, h7]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by norm_num) hE) hR
end Lean4LPD
