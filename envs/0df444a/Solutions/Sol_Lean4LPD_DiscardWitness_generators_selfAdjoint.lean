-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.generators_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:38.808402+00:00
-- url     : https://prove2.me/submissions/9ff084bb-bb1a-4e92-8016-cac95e33cdaa

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_G
public import Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_Q

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution (g : ℕ) : IsSelfAdjoint (Gs g) := by
  unfold Gs
  split
  · exact isSelfAdjoint_G
  · exact isSelfAdjoint_Q
end Lean4LPD.DiscardWitness
