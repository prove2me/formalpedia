-- Prove2me | solution 1 for Lean4LPD.two_lt_cZero_of_m_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:26.314747+00:00
-- url     : https://prove2.me/submissions/a96eb64f-3d52-40b9-a87f-2d217a40bf1e

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
theorem _root_.solution : Admissible 5 0 2 ∧ (5 : ℝ) ≥ 5 ∧ 2 < cZero 5 0 2 1 := by
  refine ⟨⟨by norm_num, le_refl 0, by norm_num, by norm_num, by norm_num⟩, le_refl 5, ?_⟩
  have hroot : (1 + (1 : ℝ)) ^ ((1 : ℝ) / (0 + 1)) = 2 := by
    norm_num
  have hexp : (1 : ℝ) ≤ exp (9 / 4 * (0 + 1) / (5 * 2)) :=
    Real.one_le_exp (by norm_num)
  have hval : cZero 5 0 2 1 = 6 / 5 * exp (9 / 4 * (0 + 1) / (5 * 2)) * 2 := by
    unfold cZero
    rw [hroot]
    norm_num
  rw [hval]
  nlinarith only [hexp]
end Lean4LPD
