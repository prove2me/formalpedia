-- Prove2me | solution 1 for Lean4LPD.chain_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:52.482139+00:00
-- url     : https://prove2.me/submissions/bb6f70ce-ab58-4d93-9ad1-2b35ebe3231d

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
namespace Lean4LPD
theorem _root_.solution (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (k m : ℕ) :
    chain eps E (k + 2) m = ∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j) := rfl
end Lean4LPD
