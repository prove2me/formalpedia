-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discarded_eq_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:08.428797+00:00
-- url     : https://prove2.me/submissions/55df4c3a-3f44-4ce0-acf7-d6547d7d4a45

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_cutoff_Q

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q) = toMatrix Q := by
  rw [cutoff_Q, sub_zero]
end Lean4LPD.DiscardWitness
