-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.pf2_named_P6_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:53:28.148292+00:00
-- url     : https://prove2.me/submissions/53608f67-979c-445d-b287-17cfae375bc7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
public import Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_coeff_sines
public import Theorems.Thm_Lean4LPD_LayerCounterexample_herm_P6_sign
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_iPow_two
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.iPow_two



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) • toMatrix (herm (cls P₆)) =
      ((Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2) • toMatrix P₆ := by
  rw [pf2_coeff_sines, herm_P6_sign, toMatrix_phaseMul, iPow_two, smul_smul]
  congr 1
  ring
end Lean4LPD.LayerCounterexample
