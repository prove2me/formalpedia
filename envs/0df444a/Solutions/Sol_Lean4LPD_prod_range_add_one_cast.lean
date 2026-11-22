-- Prove2me | solution 1 for Lean4LPD.prod_range_add_one_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:10.152815+00:00
-- url     : https://prove2.me/submissions/bb39c86b-4280-4e29-86c1-d8460ce3dcae

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (n : ℕ) : ∏ i ∈ range n, ((i : ℝ) + 1) = (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring
end Lean4LPD
