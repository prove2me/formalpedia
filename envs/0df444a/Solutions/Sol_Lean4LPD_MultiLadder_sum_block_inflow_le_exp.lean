-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_block_inflow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:01.464934+00:00
-- url     : https://prove2.me/submissions/c4647eec-6fca-484e-8097-9e78a1620e9c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_chain_slot_sum_le_exp
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_block_inflow_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
namespace MultiLadder
theorem _root_.solution {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ}
    {M C R : ℝ} (L : MultiLadder eps E M)
    (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hR : 0 ≤ R) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G) (hW : 0 ≤ W m)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ d ∈ range r, x d G) ≤
      M * (C * W m * (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
        Real.exp (R * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  refine (MultiLadder.sum_block_inflow_le L heps hE hM hm hG r x hreset hinflow).trans ?_
  exact mul_le_mul_of_nonneg_left
    (chain_slot_sum_le_exp hm heps hC hR hW (by positivity) hentry hjump) hM
end MultiLadder
end Lean4LPD
