-- Prove2me | solution 1 for Lean4LPD.PauliString.layerStepMass_reset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:07:33.367067+00:00
-- url     : https://prove2.me/submissions/d1a8411c-60b4-4fb7-88ac-e3fa46d44379

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_layerStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    {Γ wstar ko : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    (hcut : ko ≤ wstar) (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (d : ℕ) :
    layerStepMass layers Γ wstar O d 0 = 0 := by
  rw [layerStepMass, layerBlockTraj_zero]
  cases d with
  | zero =>
    rw [layerStepTraj_zero]
    exact highNorm_eq_zero wstar fun p hp => hloc p (hcut.trans_lt hp)
  | succ d => exact highNorm_layerStepTraj_succ layers Γ wstar O d
end Lean4LPD.PauliString
