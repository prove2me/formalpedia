-- Prove2me | solution 1 for Lean4LPD.sum_range_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:39.153778+00:00
-- url     : https://prove2.me/submissions/45122908-0f1c-41fd-a7d9-a40b0ba3eaa0

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (m : ℕ) :
    ∀ g : ℕ, ∑ l ∈ range g, l.choose m = g.choose (m + 1) := by
  intro g
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    ring
end Lean4LPD
