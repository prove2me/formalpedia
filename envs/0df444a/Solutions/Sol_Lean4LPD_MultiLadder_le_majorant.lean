-- Prove2me | solution 1 for Lean4LPD.MultiLadder.le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:03.364166+00:00
-- url     : https://prove2.me/submissions/d1343786-f011-42fe-b8bf-3c30f75bfead

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_chain_succ
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_chain_shift

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
theorem _root_.solution (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) :
    ∀ T : ℕ, ∀ m : ℕ, 1 ≤ m → L.N m T ≤ majorant eps E M m T := by
  intro T
  induction T with
  | zero =>
    intro m hm
    simp [majorant, L.init m hm]
  | succ T ih =>
    intro m hm
    have hstep := L.step m T hm
    have hmain : L.N m T ≤ M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m := ih m hm
    have hlower : ∀ j ∈ Ico 1 m, eps j m * L.N (m - j) T
        ≤ eps j m * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact mul_le_mul_of_nonneg_left (ih (m - j) (by omega)) (heps j m)
    have hsum : ∑ j ∈ Ico 1 m, eps j m * L.N (m - j) T
        ≤ ∑ j ∈ Ico 1 m, eps j m
            * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)) :=
      Finset.sum_le_sum hlower
    have hfactor : ∑ j ∈ Ico 1 m, eps j m
          * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))
        = M * ∑ j ∈ Ico 1 m, eps j m
            * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [majorant, sum_chain_succ, sum_chain_shift]
    calc L.N m (T + 1)
        ≤ L.N m T + (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) T) + E m * M := hstep
      _ ≤ (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
            + (M * ∑ j ∈ Ico 1 m, eps j m
                * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))
            + E m * M := by
          rw [← hfactor]; linarith [hsum, hmain]
      _ = M * ((∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
            + (E m + ∑ j ∈ Ico 1 m, eps j m
                * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))) := by ring
end Lean4LPD.MultiLadder
