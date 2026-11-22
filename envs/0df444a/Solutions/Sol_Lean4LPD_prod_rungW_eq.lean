-- Prove2me | solution 1 for Lean4LPD.prod_rungW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:31.650405+00:00
-- url     : https://prove2.me/submissions/77c17ff0-9892-41c5-9fa9-c81de8fe8d6a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (kh1 c : ℝ) (n : ℕ) :
    ∏ i ∈ range n, rungW kh1 c (i + 2) = kh1 ^ n * ∏ i ∈ range n, ((i : ℝ) + 1 + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
    have hr : rungW kh1 c (n + 2) = kh1 * ((n : ℝ) + 1 + c) := by
      unfold rungW; push_cast; ring
    rw [hr, pow_succ]
    ring
end Lean4LPD
