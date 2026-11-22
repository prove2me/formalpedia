-- Prove2me | solution 1 for Lean4LPD.prod_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:23.306602+00:00
-- url     : https://prove2.me/submissions/1e60ab61-fd86-4c33-b96e-7b784cb697bf

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤ ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · linarith
end Lean4LPD
