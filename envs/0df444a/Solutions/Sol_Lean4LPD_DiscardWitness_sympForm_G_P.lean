-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.sympForm_G_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:21.477974+00:00
-- url     : https://prove2.me/submissions/9fde5116-5213-450b-8b90-4a275fbabcc1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : sympForm G P = 1 := by decide
end Lean4LPD.DiscardWitness
