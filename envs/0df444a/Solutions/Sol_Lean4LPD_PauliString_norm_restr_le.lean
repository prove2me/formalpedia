-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_restr_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:33.46406+00:00
-- url     : https://prove2.me/submissions/fc1b22d1-2bcc-4393-91ea-c341c1bc01d2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_sq

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr S y‖ ≤ ‖y‖ := by
  have h : ‖restr S y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_restr_sq, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      fun p _ _ => by positivity
  nlinarith [norm_nonneg (restr S y), norm_nonneg y]
end Lean4LPD.PauliString
