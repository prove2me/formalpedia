-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_chain_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:37.642824+00:00
-- url     : https://prove2.me/submissions/39790b26-58d2-47b2-b2e0-f1c077efd783

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump

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
theorem _root_.solution (m T : ℕ) :
    ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m
      = (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
        + ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by
  have hpeel : ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (T + 1), ((T + 1).choose (k + 1) : ℝ) * chain eps E (k + 1) m := by
    rw [Finset.sum_range_succ' (fun k => ((T + 1).choose k : ℝ) * chain eps E k m)]
    simp
  have hpascal : ∀ k ∈ range (T + 1),
      ((T + 1).choose (k + 1) : ℝ) * chain eps E (k + 1) m
        = (T.choose k : ℝ) * chain eps E (k + 1) m
          + (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m := by
    intro k _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have htail : ∑ k ∈ range (T + 1), (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m
      = ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m := by
    rw [Finset.sum_range_succ (fun k => (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m),
      Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E k m)]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hpeel, Finset.sum_congr rfl hpascal, Finset.sum_add_distrib, htail]
  ring
end Lean4LPD.MultiLadder
