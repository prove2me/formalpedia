-- Prove2me | solution 1 for Lean4LPD.LayerWitness.weight_Z_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:57.260906+00:00
-- url     : https://prove2.me/submissions/208c2666-369a-40f5-88ba-7e4f79176104

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution : weight (Z (3 : Fin 8)) = 1 := by decide
end Lean4LPD.LayerWitness
