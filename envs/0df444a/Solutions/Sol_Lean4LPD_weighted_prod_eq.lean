-- Prove2me | solution 1 for Lean4LPD.weighted_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:13.651824+00:00
-- url     : https://prove2.me/submissions/f0b9f325-04fa-4820-945b-54d902887540

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
namespace Lean4LPD
theorem _root_.solution (w : ℕ → ℝ) (a : ℝ) :
    ∀ m : ℕ, (∏ j ∈ Finset.Icc 1 m, w (j + 1) * a) = a ^ m * ∏ j ∈ Finset.Icc 2 (m + 1), w j := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ∏ j ∈ Finset.Icc 1 (m + 1), w (j + 1) * a
        = (∏ j ∈ Finset.Icc 1 m, w (j + 1) * a) * (w (m + 2) * a) :=
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) _
    have h2 : ∏ j ∈ Finset.Icc 2 (m + 2), w j = (∏ j ∈ Finset.Icc 2 (m + 1), w j) * w (m + 2) :=
      Finset.prod_Icc_succ_top (by omega) w
    rw [h1, ih, h2]; ring
end Lean4LPD
