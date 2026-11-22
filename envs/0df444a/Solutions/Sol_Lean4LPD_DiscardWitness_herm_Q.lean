-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.herm_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:24.653842+00:00
-- url     : https://prove2.me/submissions/3f59d535-d2e0-4abc-98f2-1db6d8e4d14a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : herm (cls Q) = Q := by decide
end Lean4LPD.DiscardWitness
