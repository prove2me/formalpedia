-- Prove2me | solution 1 for Lean4LPD.prod_shift_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:23.84927+00:00
-- url     : https://prove2.me/submissions/3c0e3f75-0267-42ca-85b5-d59ffb57d78e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (c : ℝ) (n : ℕ) :
    (∏ i ∈ range n, ((i : ℝ) + 2 + c)) * (1 + c)
      = (∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast
    calc (∏ i ∈ range n, ((i : ℝ) + 2 + c)) * ((n : ℝ) + 2 + c) * (1 + c)
        = ((∏ i ∈ range n, ((i : ℝ) + 2 + c)) * (1 + c)) * ((n : ℝ) + 2 + c) := by ring
      _ = ((∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c)) * ((n : ℝ) + 2 + c) := by
          rw [ih]
      _ = (∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c) * ((n : ℝ) + 1 + 1 + c) := by
          ring
end Lean4LPD
