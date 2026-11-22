-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.herm_P6_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:32.699275+00:00
-- url     : https://prove2.me/submissions/68b727a1-40e7-4d1c-adc9-f6437e427eaf

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution : herm (cls P₆) = phaseMul 2 P₆ := by decide
end Lean4LPD.LayerCounterexample
