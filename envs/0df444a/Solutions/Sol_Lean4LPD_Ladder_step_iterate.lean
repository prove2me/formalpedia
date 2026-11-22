-- Prove2me | solution 1 for Lean4LPD.Ladder.step_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:47.715893+00:00
-- url     : https://prove2.me/submissions/fbc6a0a1-54ee-49c2-9450-9015257315db

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Recursion
public import Theorems.Thm_Lean4LPD_rungWeight_one
attribute [local simp] Lean4LPD.rungWeight_one



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.Ladder
open Finset
variable {a M : ℝ} (L : Ladder a M)
namespace Lean4LPD.Ladder
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ a * ∑ l ∈ range g, L.N (m - 1) l := by
  intro g
  induction g with
  | zero => simp [L.init m hm]
  | succ g ih =>
    calc L.N m (g + 1)
        ≤ L.N m g + a * L.N (m - 1) g := L.step m g hm
      _ ≤ (a * ∑ l ∈ range g, L.N (m - 1) l) + a * L.N (m - 1) g := by linarith
      _ = a * ∑ l ∈ range (g + 1), L.N (m - 1) l := by
          rw [Finset.sum_range_succ]; ring
end Lean4LPD.Ladder
