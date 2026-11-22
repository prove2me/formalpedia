-- Prove2me | solution 1 for Lean4LPD.MultiLadder.majorant_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:38.388968+00:00
-- url     : https://prove2.me/submissions/f4d22991-241e-42ba-8700-c53ddf050e66

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Theorems.Thm_Lean4LPD_chain_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
open Lean4LPD.MultiLadder
variable {M : ℝ}
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) (m T : ℕ) :
    majorant eps E M m T ≤ majorant eps E M m (T + 1) := by
  have hchoose : ∀ k, (T.choose k : ℝ) ≤ ((T + 1).choose k : ℝ) := by
    intro k
    have hn : T.choose k ≤ (T + 1).choose k := by
      match k with
      | 0 => simp
      | (k + 1) => rw [Nat.choose_succ_succ]; exact Nat.le_add_left _ _
    exact_mod_cast hn
  refine mul_le_mul_of_nonneg_left ?_ hM
  calc ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m
      ≤ ∑ k ∈ range (T + 1), ((T + 1).choose k : ℝ) * chain eps E k m :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hchoose k) (chain_nonneg heps hE k m)
    _ ≤ ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))
          fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (chain_nonneg heps hE k m)
end Lean4LPD.MultiLadder
