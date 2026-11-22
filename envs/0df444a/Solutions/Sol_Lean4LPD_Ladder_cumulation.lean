-- Prove2me | solution 1 for Lean4LPD.Ladder.cumulation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:53.649842+00:00
-- url     : https://prove2.me/submissions/d14b1a73-f01d-471e-99cc-d505a608e283

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Recursion
public import Theorems.Thm_Lean4LPD_Ladder_step_iterate
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_sum_range_choose_real
attribute [local simp] Lean4LPD.rungWeight_one



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.Ladder
open Finset
variable {a M : ℝ} (L : Ladder a M)
namespace Lean4LPD.Ladder
theorem _root_.solution (ha : 0 ≤ a) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * a ^ m * M := by
  intro m
  induction m with
  | zero => intro g; simpa using L.reservoir g
  | succ m ih =>
    intro g
    have hm : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have h1 : L.N (m + 1) g ≤ a * ∑ l ∈ range g, L.N m l := by
      simpa using L.step_iterate hm g
    have h2 : ∑ l ∈ range g, L.N m l ≤ ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M) :=
      Finset.sum_le_sum fun l _ => ih l
    have h3 : ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M)
        = (g.choose (m + 1) : ℝ) * a ^ m * M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_range_choose_real]
    calc L.N (m + 1) g
        ≤ a * ∑ l ∈ range g, L.N m l := h1
      _ ≤ a * ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M) := by
          exact mul_le_mul_of_nonneg_left h2 ha
      _ = (g.choose (m + 1) : ℝ) * a ^ (m + 1) * M := by rw [h3]; ring
end Lean4LPD.Ladder
