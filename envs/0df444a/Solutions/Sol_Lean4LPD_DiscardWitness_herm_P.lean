-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.herm_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:31.673171+00:00
-- url     : https://prove2.me/submissions/6b317f00-7012-4f2c-b4d8-d29835b44bd9

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : herm (cls P) = P := by decide
end Lean4LPD.DiscardWitness
