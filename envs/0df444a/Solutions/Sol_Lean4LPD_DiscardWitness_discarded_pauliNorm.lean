-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discarded_pauliNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:38.353931+00:00
-- url     : https://prove2.me/submissions/8556a939-da0c-4226-b36e-c82ee0715030

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_discarded_eq_Q
public import Theorems.Thm_Lean4LPD_DiscardWitness_Q_pauliNorm

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution :
    pauliNorm (toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q)) = 1 := by
  rw [discarded_eq_Q, Q_pauliNorm]
end Lean4LPD.DiscardWitness
