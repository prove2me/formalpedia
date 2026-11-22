-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.herm_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:14.807469+00:00
-- url     : https://prove2.me/submissions/e011cf83-a469-465f-8082-c93f7a87ec3c

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution : herm (cls (Z (3 : Fin 8))) = Z 3 := by decide
end Lean4LPD.LayerCounterexample
