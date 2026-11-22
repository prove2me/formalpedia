-- Prove2me | solution 1 for Lean4LPD.WeightedLadder.step_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:10.430216+00:00
-- url     : https://prove2.me/submissions/a70a11f1-32fd-41c2-8f0d-18b3aa43defc

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.WeightedLadder
variable {c : ℕ → ℝ} {M : ℝ} (L : WeightedLadder c M)
namespace Lean4LPD.WeightedLadder
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ c m * ∑ l ∈ range g, L.N (m - 1) l := by
  intro g
  induction g with
  | zero => simp [L.init m hm]
  | succ g ih =>
    calc L.N m (g + 1)
        ≤ L.N m g + c m * L.N (m - 1) g := L.step m g hm
      _ ≤ (c m * ∑ l ∈ range g, L.N (m - 1) l) + c m * L.N (m - 1) g := by linarith
      _ = c m * ∑ l ∈ range (g + 1), L.N (m - 1) l := by
          rw [Finset.sum_range_succ]; ring
end Lean4LPD.WeightedLadder
