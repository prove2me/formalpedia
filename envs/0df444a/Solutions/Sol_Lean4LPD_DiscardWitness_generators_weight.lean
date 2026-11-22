-- Prove2me | solution 1 for Lean4LPD.DiscardWitness.generators_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:41.596829+00:00
-- url     : https://prove2.me/submissions/c99ba2dc-f823-430c-9dd4-982a90d57f0b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
public import Theorems.Thm_Lean4LPD_DiscardWitness_weight_G
public import Theorems.Thm_Lean4LPD_DiscardWitness_weight_Q

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString
namespace Lean4LPD.DiscardWitness
theorem _root_.solution (g : ℕ) : weight (Gs g) = 2 := by
  unfold Gs
  split
  · exact weight_G
  · exact weight_Q
end Lean4LPD.DiscardWitness
