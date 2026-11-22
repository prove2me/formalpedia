-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.phaseMul_G_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:27.88479+00:00
-- url     : https://prove2.me/submissions/87579eb6-03f1-47ba-9ab7-cb066cf24239

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : phaseMul 1 (G * P) = Q := by decide
end Lean4LPD.DiscardWitness
