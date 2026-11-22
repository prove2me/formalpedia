-- Prove2me | solution 1 for Lean4LPD.two_lt_cZero_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:19.357406+00:00
-- url     : https://prove2.me/submissions/bb34338f-9d18-4c4e-b316-11966f763bac

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
    Admissible 1 1 32 ∧ 2 < cZero 1 1 32 0 := by
  refine ⟨⟨le_refl 1, by norm_num, by norm_num, le_refl 1, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) < exp (9 / 4 * (1 + 1) / (1 * 32)) := by
    have h := Real.add_one_le_exp (9 / 4 * (1 + 1) / (1 * 32) : ℝ)
    have harg : (9 : ℝ) / 4 * (1 + 1) / (1 * 32) = 9 / 64 := by norm_num
    rw [harg] at h
    linarith
  have hroot : (1 + (0:ℝ)) ^ ((1 : ℝ) / (1 + 1)) = 1 := by norm_num
  have : cZero 1 1 32 0 = 2 * exp (9 / 4 * (1 + 1) / (1 * 32)) := by
    unfold cZero; rw [hroot]; norm_num
  rw [this]; linarith
end Lean4LPD
