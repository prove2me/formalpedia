-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.pf2_coeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:53:27.653196+00:00
-- url     : https://prove2.me/submissions/c9e1afaa-6739-499e-80af-2a96105327c3

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
public import Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_coeff_sines

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution {θ : ℝ} (hθ : 0 < θ) (hθπ : 2 * θ < Real.pi) :
    coeff (pf2Output θ) (cls P₆) ≠ 0 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hs2 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by positivity) hθπ
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hs2C : (Real.sin (2 * θ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs2
  rw [pf2_coeff_sines]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hsC)) (pow_ne_zero 2 hs2C)
end Lean4LPD.LayerCounterexample
