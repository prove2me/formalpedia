-- Prove2me | solution 1 for Lean4LPD.chain_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:42.969799+00:00
-- url     : https://prove2.me/submissions/916be502-5e7f-46cc-9b13-e89512f073ae

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
theorem _root_.solution (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) :
    ∀ k m : ℕ, 0 ≤ chain eps E k m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro m; simp
    | 1 => intro m; simpa using hE m
    | (k + 2) =>
      intro m
      rw [chain_succ_succ]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (heps j m) (ih (k + 1) (by omega) (m - j))
end Lean4LPD
