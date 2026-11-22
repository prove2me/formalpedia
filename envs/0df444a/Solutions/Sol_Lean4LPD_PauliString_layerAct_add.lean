-- Prove2me | solution 1 for Lean4LPD.PauliString.layerAct_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:22.153421+00:00
-- url     : https://prove2.me/submissions/6ab29ee3-5293-4fbc-bc3d-8bd1d25ebaae

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ))
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    layerAct L (y + z) = layerAct L y + layerAct L z := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    rw [layerAct, ih, rotAct_add]
    rfl
end Lean4LPD.PauliString
