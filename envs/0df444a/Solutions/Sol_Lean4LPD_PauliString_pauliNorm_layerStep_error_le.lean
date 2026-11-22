-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_layerStep_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:08:36.295907+00:00
-- url     : https://prove2.me/submissions/7f0d453d-3d19-44fe-963b-64c0ed0560dc

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_layerStep_telescoping
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerBlockEnd_pow
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sum_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) (Γ wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O - layerStepTraj layers Γ wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedLayerStep layers Γ wstar O d) := by
  rw [layerStep_telescoping]
  refine (pauliNorm_sum_le _ _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun d _ => pauliNorm_layerBlockEnd_pow layers hherm Γ _ _)
end Lean4LPD.PauliString
