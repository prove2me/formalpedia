-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.weight_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:20.978078+00:00
-- url     : https://prove2.me/submissions/31e97790-6bec-4c2a-a651-49b4a416225a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : weight P = 1 := by decide
end Lean4LPD.DiscardWitness
