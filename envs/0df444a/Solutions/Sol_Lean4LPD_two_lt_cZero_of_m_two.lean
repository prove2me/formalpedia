-- Prove2me | solution 1 for Lean4LPD.two_lt_cZero_of_m_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:56.177747+00:00
-- url     : https://prove2.me/submissions/9c58b7d5-a696-4c71-83d4-ac3c86695312

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
theorem _root_.solution : Admissible 2 2 36 ∧ 2 < cZero 2 2 36 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) + 3 / 32 ≤ exp (9 / 4 * (2 + 1) / (2 * 36)) := by
    have h := Real.add_one_le_exp (9 / 4 * (2 + 1) / (2 * 36) : ℝ)
    have harg : (9 : ℝ) / 4 * (2 + 1) / (2 * 36) = 3 / 32 := by norm_num
    rw [harg] at h; linarith
  have hroot : (1.259 : ℝ) ≤ (1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1)) := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg (by norm_num) _) ?_
    have h3 : ((1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1))) ^ (3 : ℕ) = 2 := by
      rw [← Real.rpow_natCast ((1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1))) 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h3]; norm_num
  have hexppos : (0 : ℝ) < exp (9 / 4 * (2 + 1) / (2 * 36)) := Real.exp_pos _
  unfold cZero
  norm_num
  nlinarith only [hexp, hroot, hexppos]
end Lean4LPD
