-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.weight_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:39.598872+00:00
-- url     : https://prove2.me/submissions/732bd674-398d-47cf-a129-d6950abf0298

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : weight Q = 2 := by decide
end Lean4LPD.DiscardWitness
