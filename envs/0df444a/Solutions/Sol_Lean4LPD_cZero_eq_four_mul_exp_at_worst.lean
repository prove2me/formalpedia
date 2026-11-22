-- Prove2me | solution 1 for Lean4LPD.cZero_eq_four_mul_exp_at_worst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:07.851887+00:00
-- url     : https://prove2.me/submissions/cc195367-6d86-4660-a1b0-1088e5d2c16e

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
    Admissible 1 0 8 ∧ cZero 1 0 8 1 = 4 * exp (9 / 32) := by
  refine ⟨⟨le_refl 1, le_refl 0, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hroot : (1 + (1 : ℝ)) ^ ((1 : ℝ) / (0 + 1)) = 2 := by norm_num
  have harg : (9 : ℝ) / 4 * (0 + 1) / (1 * 8) = 9 / 32 := by norm_num
  unfold cZero
  rw [hroot, harg]
  ring
end Lean4LPD
