-- Prove2me | solution 1 for Lean4LPD.WeightedLadder.cumulation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:05.868617+00:00
-- url     : https://prove2.me/submissions/d88b5f01-5b78-4676-bda3-0f806bae02de

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Theorems.Thm_Lean4LPD_WeightedLadder_step_iterate
public import Theorems.Thm_Lean4LPD_sum_range_choose_real


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.WeightedLadder
variable {c : ℕ → ℝ} {M : ℝ} (L : WeightedLadder c M)
namespace Lean4LPD.WeightedLadder
theorem _root_.solution (hc : ∀ j, 0 ≤ c j) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by
  intro m
  induction m with
  | zero => intro g; simpa using L.reservoir g
  | succ m ih =>
    intro g
    have hm : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have h1 : L.N (m + 1) g ≤ c (m + 1) * ∑ l ∈ range g, L.N m l := by
      simpa using L.step_iterate hm g
    have h2 : ∑ l ∈ range g, L.N m l
        ≤ ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M) :=
      Finset.sum_le_sum fun l _ => ih l
    have h3 : ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M)
        = (g.choose (m + 1) : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_range_choose_real]
    have h4 : ∏ j ∈ Icc 1 (m + 1), c j = (∏ j ∈ Icc 1 m, c j) * c (m + 1) :=
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) c
    calc L.N (m + 1) g
        ≤ c (m + 1) * ∑ l ∈ range g, L.N m l := h1
      _ ≤ c (m + 1) * ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M) :=
          mul_le_mul_of_nonneg_left h2 (hc (m + 1))
      _ = (g.choose (m + 1) : ℝ) * (∏ j ∈ Icc 1 (m + 1), c j) * M := by
          rw [h3, h4]; ring
end Lean4LPD.WeightedLadder
