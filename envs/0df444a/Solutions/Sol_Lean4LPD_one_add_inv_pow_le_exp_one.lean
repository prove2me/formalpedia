-- Prove2me | solution 1 for Lean4LPD.one_add_inv_pow_le_exp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:29.06034+00:00
-- url     : https://prove2.me/submissions/2d50f25f-18dc-4c41-b344-85a67a041e90

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} (hj : 1 ≤ j) :
    (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hb : (1 : ℝ) + 1 / (j : ℝ) ≤ Real.exp (1 / (j : ℝ)) := by
    have := Real.add_one_le_exp (1 / (j : ℝ))
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 1 / (j : ℝ) := by positivity
  calc (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp (1 / (j : ℝ)) ^ j :=
        pow_le_pow_left₀ hb0 hb j
    _ = Real.exp ((j : ℝ) * (1 / (j : ℝ))) := (Real.exp_nat_mul _ j).symm
    _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hjpos)]
end Lean4LPD
