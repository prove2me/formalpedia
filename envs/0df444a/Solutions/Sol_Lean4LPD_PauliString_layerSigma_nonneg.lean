-- Prove2me | solution 1 for Lean4LPD.PauliString.layerSigma_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:07.270564+00:00
-- url     : https://prove2.me/submissions/2b16dbaf-f302-494b-ab15-12c632f62cd3

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
theorem _root_.solution (L : List (PauliString n × ℝ)) : 0 ≤ layerSigma L := by
  cases L with
  | nil => exact le_rfl
  | cons g L => exact (abs_nonneg _).trans (le_max_left _ _)
end Lean4LPD.PauliString
