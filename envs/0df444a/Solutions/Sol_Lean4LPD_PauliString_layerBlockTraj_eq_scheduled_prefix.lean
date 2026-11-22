-- Prove2me | solution 1 for Lean4LPD.PauliString.layerBlockTraj_eq_scheduled_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:10:12.253852+00:00
-- url     : https://prove2.me/submissions/c9605261-25ee-4011-a87e-83e58e2dac87

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_within_step
public import Theorems.Thm_Lean4LPD_PauliString_layerScheduledTraj_at_boundary

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d i : ℕ) (hi : i < Γ) :
    layerBlockTraj layers (layerStepTraj layers Γ wstar O d) i =
      layerScheduledTraj layers Γ wstar O (d * Γ + i) := by
  rw [layerScheduledTraj_within_step layers Γ wstar O d i hi,
    layerScheduledTraj_at_boundary layers Γ wstar O d (by omega)]
end Lean4LPD.PauliString
