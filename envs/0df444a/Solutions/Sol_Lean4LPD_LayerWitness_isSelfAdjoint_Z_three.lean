-- Prove2me | solution 1 for Lean4LPD.LayerWitness.isSelfAdjoint_Z_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:31.86346+00:00
-- url     : https://prove2.me/submissions/d345ee05-0607-4b5d-979c-f3a4a106d4d0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution : IsSelfAdjoint (Z (3 : Fin 8)) :=
  isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.LayerWitness
