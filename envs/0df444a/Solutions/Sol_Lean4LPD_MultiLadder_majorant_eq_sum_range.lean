-- Prove2me | solution 1 for Lean4LPD.MultiLadder.majorant_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:43.02003+00:00
-- url     : https://prove2.me/submissions/d539715a-84e2-4993-8143-d4b695188612

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Assembly
public import Theorems.Thm_Lean4LPD_chain_eq_zero_of_lt


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    majorant eps E M m T = M * ∑ k ∈ range (m + 1), (T.choose k : ℝ) * chain eps E k m := by
  have hvanish_chain : ∀ k ∈ range (max (T + 1) (m + 1)), k ∉ range (m + 1) →
      (T.choose k : ℝ) * chain eps E k m = 0 := by
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [chain_eq_zero_of_lt k m hm (by omega), mul_zero]
  have hvanish_choose : ∀ k ∈ range (max (T + 1) (m + 1)), k ∉ range (T + 1) →
      (T.choose k : ℝ) * chain eps E k m = 0 := by
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hT : ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (max (T + 1) (m + 1)), (T.choose k : ℝ) * chain eps E k m :=
    Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_max_left _ _))) hvanish_choose
  have hm' : ∑ k ∈ range (m + 1), (T.choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (max (T + 1) (m + 1)), (T.choose k : ℝ) * chain eps E k m :=
    Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_max_right _ _))) hvanish_chain
  unfold majorant
  rw [hT, ← hm']
end Lean4LPD.MultiLadder
