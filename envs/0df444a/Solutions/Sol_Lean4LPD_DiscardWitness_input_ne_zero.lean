-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.input_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:19.969999+00:00
-- url     : https://prove2.me/submissions/ff6188d7-26e9-4635-88a8-9276f603b293

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : toMatrix P ≠ 0 := toMatrix_ne_zero P
end Lean4LPD.DiscardWitness
