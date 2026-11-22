-- Prove2me | solution 1 for Lean4LPD.chain_slot_sum_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:09.861865+00:00
-- url     : https://prove2.me/submissions/466822c5-2ac7-44cc-90d0-5ba26e22b2ae

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_slot_polynomial_le_exp
public import Theorems.Thm_Lean4LPD_chain_le_weighted_choose


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R X : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hW : 0 ≤ W m) (hX : 0 < X)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      chain eps E (k + 1) m) ≤
      C * W m * X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by
  calc
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
        chain eps E (k + 1) m) ≤
        ∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
          (C * R ^ (m - (k + 1)) * W m * ((m - 1).choose k : ℝ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left
        (chain_le_weighted_choose heps hC hR hentry hjump k m hm) (by positivity)
    _ = C * W m * ∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
        R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    _ ≤ C * W m * (X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X)) :=
      mul_le_mul_of_nonneg_left (slot_polynomial_le_exp hm hX hR) (mul_nonneg hC hW)
    _ = C * W m * X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by ring
end Lean4LPD
