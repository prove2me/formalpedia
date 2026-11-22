-- Prove2me | solution 1 for Lean4LPD.prod_shifted_le_factorial_exp_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:43.47879+00:00
-- url     : https://prove2.me/submissions/2dd82903-2021-4f64-9e78-79dd345f746f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_prod_add_one_le_factorial_exp_rpow
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 2 + c) ≤
      (Nat.factorial (n + 1) : ℝ) * (Real.exp 1 * ((n : ℝ) + 1)) ^ c := by
  have hnonneg : 0 ≤ ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
    apply Finset.prod_nonneg
    intro i _
    positivity
  have hsplit : ∏ i ∈ range (n + 1), ((i : ℝ) + 1 + c) =
      (1 + c) * ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
    rw [Finset.prod_range_succ']
    simp_rw [Nat.cast_add, Nat.cast_one,
      show ∀ i : ℕ, (i : ℝ) + 1 + 1 + c = (i : ℝ) + 2 + c from fun i => by ring]
    simp [mul_comm]
  have hle : ∏ i ∈ range n, ((i : ℝ) + 2 + c) ≤
      ∏ i ∈ range (n + 1), ((i : ℝ) + 1 + c) := by
    rw [hsplit]
    nlinarith [mul_nonneg hc hnonneg]
  exact hle.trans (by
    simpa only [Nat.cast_add, Nat.cast_one] using
      prod_add_one_le_factorial_exp_rpow hc (n + 1) (by omega))
end Lean4LPD
