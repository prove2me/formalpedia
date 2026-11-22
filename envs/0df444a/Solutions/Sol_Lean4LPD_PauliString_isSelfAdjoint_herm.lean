-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_herm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:47.15948+00:00
-- url     : https://prove2.me/submissions/ee2da737-9975-4eb7-b523-9f0b628887eb

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (p : PauliIndex n) : IsSelfAdjoint (herm p) :=
  isSelfAdjoint_iff_phase.2 rfl
end Lean4LPD.PauliString
