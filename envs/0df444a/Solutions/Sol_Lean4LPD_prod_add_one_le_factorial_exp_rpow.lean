-- Prove2me | solution 1 for Lean4LPD.prod_add_one_le_factorial_exp_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:54.119621+00:00
-- url     : https://prove2.me/submissions/394b3c0d-170b-4b15-9cf7-7744a8dd68b5

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_prod_range_add_one_cast
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤
      (Nat.factorial n : ℝ) * (Real.exp 1 * (n : ℝ)) ^ c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : ∏ i ∈ range n, ((i : ℝ) + 1 + c) =
      (Nat.factorial n : ℝ) * ∏ i ∈ range n, (1 + c / ((i : ℝ) + 1)) := by
    rw [← prod_range_add_one_cast, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hsum : (∑ i ∈ range n, c / ((i : ℝ) + 1)) = c * (harmonic n : ℝ) := by
    simp [harmonic, Finset.mul_sum, div_eq_mul_inv]
  have hexp : Real.exp (c * (1 + Real.log (n : ℝ))) =
      (Real.exp 1 * (n : ℝ)) ^ c := by
    rw [Real.rpow_def_of_pos (by positivity),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hnpos), Real.log_exp]
    congr 1
    ring
  calc
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) =
        (Nat.factorial n : ℝ) * ∏ i ∈ range n, (1 + c / ((i : ℝ) + 1)) := hfactor
    _ ≤ (Nat.factorial n : ℝ) * Real.exp (∑ i ∈ range n, c / ((i : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left
        (Real.prod_one_add_le_exp_sum _ fun i => div_nonneg hc (by positivity))
        (Nat.cast_nonneg _)
    _ ≤ (Nat.factorial n : ℝ) * Real.exp (c * (1 + Real.log (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      rw [hsum]
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hc
    _ = (Nat.factorial n : ℝ) * (Real.exp 1 * (n : ℝ)) ^ c := by rw [hexp]
end Lean4LPD
