-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.discarded_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:21.355806+00:00
-- url     : https://prove2.me/submissions/2642ef12-bcc3-458f-ad06-bca94fc5dc92

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_discarded_eq_Q
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution : toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q) ≠ 0 := by
  rw [discarded_eq_Q]
  exact toMatrix_ne_zero Q
end Lean4LPD.DiscardWitness
