-- Prove2me | solution 1 for Lean4LPD.partFactor_at_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:26.760249+00:00
-- url     : https://prove2.me/submissions/76cf36c9-2b1a-428d-9c5e-2a5752f9ce2f

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Theorems.Thm_Lean4LPD_prod_range_add_one_cast

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (j : ℕ) : partFactor j (j : ℝ)
    = (2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by
  unfold partFactor
  have hprod : ∏ i ∈ range j, ((j : ℝ) - j + 1 + i) = (Nat.factorial j : ℝ) := by
    rw [← prod_range_add_one_cast j]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hprod]
  congr 1
  ring
end Lean4LPD
