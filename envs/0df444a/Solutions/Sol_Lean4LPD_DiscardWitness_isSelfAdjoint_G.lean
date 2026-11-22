-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.isSelfAdjoint_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:46.013562+00:00
-- url     : https://prove2.me/submissions/79a1bcd7-5f03-4b21-95fd-068e0fa3194b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : IsSelfAdjoint G := isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.DiscardWitness
