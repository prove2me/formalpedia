-- Prove2me | solution 1 for Lean4LPD.PauliString.highNorm_layerStepTraj_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:04:37.89299+00:00
-- url     : https://prove2.me/submissions/55022555-80d5-4ea2-aa61-1281e805943e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_layerStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_truncOp_compl


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    highNorm wstar (layerStepTraj layers Γ wstar O (d + 1)) = 0 := by
  rw [layerStepTraj_succ, highNorm_truncOp_compl]
end Lean4LPD.PauliString
