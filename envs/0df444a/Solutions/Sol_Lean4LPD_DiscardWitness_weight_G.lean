-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.weight_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:15.445808+00:00
-- url     : https://prove2.me/submissions/7399e0ed-50d7-4b0a-8c2d-4942c40a1653

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : weight G = 2 := by decide
end Lean4LPD.DiscardWitness
