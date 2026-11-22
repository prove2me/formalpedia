-- Prove2me | solution 1 for Lean4LPD.exp_four_thirds_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:27.624643+00:00
-- url     : https://prove2.me/submissions/b44217f3-ff98-45d4-87f3-bb138b2b214d

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution : Real.exp (4 / 3 : ℝ) ≤ 4.03 := by
  have h12 : Real.exp (1 / 12 : ℝ) ≤ 12 / 11 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 12 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmul : Real.exp (((16 : ℕ) : ℝ) * (1 / 12 : ℝ)) = Real.exp (1 / 12 : ℝ) ^ (16 : ℕ) :=
    Real.exp_nat_mul _ 16
  have harg : ((16 : ℕ) : ℝ) * (1 / 12 : ℝ) = 4 / 3 := by norm_num
  rw [harg] at hmul
  rw [hmul]
  calc Real.exp (1 / 12 : ℝ) ^ (16 : ℕ)
      ≤ (12 / 11 : ℝ) ^ (16 : ℕ) := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h12 16
    _ ≤ 4.03 := by norm_num
end Lean4LPD
