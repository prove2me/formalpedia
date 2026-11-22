-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.isSelfAdjoint_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:08.117684+00:00
-- url     : https://prove2.me/submissions/1259d1c6-d989-4a3f-92ac-a6c77f0e190a

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
theorem _root_.solution : IsSelfAdjoint P := isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.DiscardWitness
