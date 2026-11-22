-- Prove2me | solution 1 for Lean4LPD.slot_polynomial_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:01.400721+00:00
-- url     : https://prove2.me/submissions/d9fc2413-8392-4d0d-899e-6bb68da8cc16

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_sum_factorial_sectors_le_exp
public import Theorems.Thm_Lean4LPD_slot_polynomial_eq_sectors
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) (hR : 0 ≤ R) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) ≤
      X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by
  rw [slot_polynomial_eq_sectors hm hX]
  have h := mul_le_mul_of_nonneg_left
    (sum_factorial_sectors_le_exp m (div_nonneg hR hX.le))
    (show 0 ≤ X ^ m / (Nat.factorial m : ℝ) by positivity)
  simpa only [show (m : ℝ) ^ 2 * (R / X) = R * (m : ℝ) ^ 2 / X from by ring] using h
end Lean4LPD
