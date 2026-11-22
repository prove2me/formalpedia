-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_discardedLayerStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:06:14.291848+00:00
-- url     : https://prove2.me/submissions/645d630e-28f6-463f-842d-6ce5cdd8053a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_layerStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sub_truncOp_highSet_compl


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    pauliNorm (discardedLayerStep layers Γ wstar O d) =
      highNorm wstar (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := by
  rw [discardedLayerStep, layerStepTraj_succ, pauliNorm_sub_truncOp_highSet_compl]
end Lean4LPD.PauliString
