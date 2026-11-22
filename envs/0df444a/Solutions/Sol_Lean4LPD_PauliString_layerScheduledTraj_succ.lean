-- Prove2me | solution 1 for Lean4LPD.PauliString.layerScheduledTraj_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:43.461961+00:00
-- url     : https://prove2.me/submissions/c558f585-7dbb-489d-a54d-413c1b0df612

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
    (Γ wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    layerScheduledTraj layers Γ wstar O (T + 1) = truncOp (trotterSchedule Γ wstar T)
      (layerConj (layers (T % Γ)) (layerScheduledTraj layers Γ wstar O T)) := rfl
end Lean4LPD.PauliString
