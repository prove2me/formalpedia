-- Prove2me | solution 1 for Lean4LPD.sum_range_choose_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:04.027953+00:00
-- url     : https://prove2.me/submissions/55729ea9-89ae-4066-9c0a-8ae417be5417

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Theorems.Thm_Lean4LPD_sum_range_choose

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (m g : ℕ) :
    ∑ l ∈ range g, (l.choose m : ℝ) = (g.choose (m + 1) : ℝ) := by
  rw [← Nat.cast_sum, sum_range_choose]
end Lean4LPD
