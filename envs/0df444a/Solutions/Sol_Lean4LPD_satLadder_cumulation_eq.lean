-- Prove2me | solution 1 for Lean4LPD.satLadder_cumulation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:54.522051+00:00
-- url     : https://prove2.me/submissions/fa06e0f9-2f74-4363-a7c4-464949b2b13c

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
theorem _root_.solution {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) (m g : ℕ) :
    (satLadder hc hM).N m g = (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := rfl
end Lean4LPD
