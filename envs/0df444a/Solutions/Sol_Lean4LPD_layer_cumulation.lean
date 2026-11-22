-- Prove2me | solution 1 for Lean4LPD.layer_cumulation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:54.092804+00:00
-- url     : https://prove2.me/submissions/c141c77b-946e-450f-b2c4-e75b1d32856b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Theorems.Thm_Lean4LPD_WeightedLadder_cumulation
public import Theorems.Thm_Lean4LPD_weighted_prod_eq

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {M a : ℝ} {w : ℕ → ℝ} (ha : 0 ≤ a) (hw : ∀ j, 0 ≤ w j)
    (L : WeightedLadder (fun m => w (m + 1) * a) M) (m g : ℕ) :
    L.N m g ≤ (g.choose m : ℝ) * a ^ m * (∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := by
  have h := L.cumulation (fun j => mul_nonneg (hw (j + 1)) ha) m g
  rw [weighted_prod_eq w a m] at h
  calc L.N m g ≤ (g.choose m : ℝ) * (a ^ m * ∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := h
    _ = (g.choose m : ℝ) * a ^ m * (∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := by ring
end Lean4LPD
