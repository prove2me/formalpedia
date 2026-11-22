-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discardedStep_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:42.409836+00:00
-- url     : https://prove2.me/submissions/23f0966d-eb4b-4d34-85a7-39a90abcffbd

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_zero
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : discardedStep Gs angles 2 1 (toMatrix P) 0 ≠ 0 := by
  rw [discardedStep_zero]
  exact toMatrix_ne_zero Q
end Lean4LPD.DiscardWitness
