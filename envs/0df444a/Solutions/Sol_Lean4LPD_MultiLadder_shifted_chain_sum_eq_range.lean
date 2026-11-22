-- Prove2me | solution 1 for Lean4LPD.MultiLadder.shifted_chain_sum_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:46.102459+00:00
-- url     : https://prove2.me/submissions/2494ca37-4a75-43fb-8af2-1fbaf60e4add

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_chain_eq_zero_of_lt


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m) =
      ∑ k ∈ range m, (T.choose k : ℝ) * chain eps E (k + 1) m := by
  rcases le_total (T + 1) m with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [chain_eq_zero_of_lt (k + 1) m hm (by omega), mul_zero]
end Lean4LPD.MultiLadder
