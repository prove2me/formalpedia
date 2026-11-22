-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_chain_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:19.484963+00:00
-- url     : https://prove2.me/submissions/0cfebba7-205d-49ff-b49f-efa6d259e644

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Theorems.Thm_Lean4LPD_chain_succ_succ

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
    ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m
      = E m + ∑ j ∈ Ico 1 m, eps j m
          * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
  have hpeel : ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m
      = (∑ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 2) m) + E m := by
    rw [Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E (k + 1) m)]
    simp
  have hdrop : ∀ j : ℕ, ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)
      = ∑ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 1) (m - j) := by
    intro j
    rw [Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E k (m - j))]
    simp
  have hbody : ∀ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 2) m
      = ∑ j ∈ Ico 1 m, (T.choose (k + 1) : ℝ) * (eps j m * chain eps E (k + 1) (m - j)) := by
    intro k _
    rw [chain_succ_succ, Finset.mul_sum]
  have hinner : ∀ j ∈ Ico 1 m,
      ∑ k ∈ range T, (T.choose (k + 1) : ℝ) * (eps j m * chain eps E (k + 1) (m - j))
        = eps j m * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
    intro j _
    rw [hdrop j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hpeel, Finset.sum_congr rfl hbody, Finset.sum_comm, Finset.sum_congr rfl hinner, add_comm]
end Lean4LPD.MultiLadder
