-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.isSelfAdjoint_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:36.976987+00:00
-- url     : https://prove2.me/submissions/d0cdecc0-8c45-4a49-8b25-26c666c74090

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
theorem _root_.solution : IsSelfAdjoint Q := isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.DiscardWitness
