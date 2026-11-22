-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.input_highNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:30.162543+00:00
-- url     : https://prove2.me/submissions/7a7b9275-a82e-4da7-b241-f1b4d73ce3da

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_input_local
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : highNorm 1 (toMatrix P) = 0 := highNorm_eq_zero 1 input_local
end Lean4LPD.DiscardWitness
