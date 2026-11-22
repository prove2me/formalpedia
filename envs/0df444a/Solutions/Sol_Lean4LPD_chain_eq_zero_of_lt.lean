-- Prove2me | solution 1 for Lean4LPD.chain_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:20.834028+00:00
-- url     : https://prove2.me/submissions/0ceeb85a-4587-4f4f-9303-63fb938adc1f

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
namespace Lean4LPD
theorem _root_.solution : ∀ k m : ℕ, 1 ≤ m → m < k → chain eps E k m = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro m _ h; exact absurd h (by omega)
    | 1 => intro m h1 h2; omega
    | (k + 2) =>
      intro m h1 h2
      rw [chain_succ_succ]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      rw [ih (k + 1) (by omega) (m - j) (by omega) (by omega), mul_zero]
end Lean4LPD
