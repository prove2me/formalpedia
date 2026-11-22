-- Prove2me | solution 1 for Lean4LPD.PauliString.layerStepTraj_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:02:39.81593+00:00
-- url     : https://prove2.me/submissions/fc8faca5-8434-4eef-8529-06bbcf4959ec

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    layerStepTraj layers Γ wstar O (d + 1) = truncOp (highSet n wstar)ᶜ
      (layerBlockTraj layers (layerStepTraj layers Γ wstar O d) Γ) := rfl
end Lean4LPD.PauliString
