-- Prove2me | solution 1 for Lean4LPD.sum_factorial_sectors_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:06.306356+00:00
-- url     : https://prove2.me/submissions/ad8798c6-d97b-417e-b6e4-a528c029fec8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_factorial_ratio_le_pow
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ D ∈ range m, ((m - 1).choose D : ℝ) *
      ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * y ^ D) ≤
      Real.exp ((m : ℝ) ^ 2 * y) := by
  refine le_trans (Finset.sum_le_sum fun D hD => ?_)
    (Real.sum_le_exp_of_nonneg (by positivity) m)
  have hD' : D ≤ m := (Finset.mem_range.mp hD).le
  have hchoose : ((m - 1).choose D : ℝ) ≤
      (m : ℝ) ^ D / (Nat.factorial D : ℝ) := by
    refine le_trans (Nat.choose_le_pow_div (α := ℝ) D (m - 1)) ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.sub_le m 1
  have hprod := mul_le_mul hchoose (factorial_ratio_le_pow hD')
    (by positivity) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right hprod (pow_nonneg hy D)) ?_
  simp only [sq, mul_pow]
  exact le_of_eq (by ring)
end Lean4LPD
