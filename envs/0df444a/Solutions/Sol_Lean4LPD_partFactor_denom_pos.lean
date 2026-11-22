-- Prove2me | solution 1 for Lean4LPD.partFactor_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:08.765109+00:00
-- url     : https://prove2.me/submissions/cf67cd82-e7d9-4749-bf67-981d14587b01

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} {s : ℝ} (hs : (j : ℝ) ≤ s) :
    0 < ∏ i ∈ range j, (s - j + 1 + i) := by
  refine Finset.prod_pos fun i _ => ?_
  have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith
end Lean4LPD
