-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.pf2_coeff_sines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:58.203343+00:00
-- url     : https://prove2.me/submissions/c510c735-0d95-469b-b4c9-89456dd922eb

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
public import Theorems.Thm_Lean4LPD_LayerCounterexample_pf2_coeff_polynomial

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -(Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2 := by
  rw [pf2_coeff_polynomial, Real.sin_two_mul]
  push_cast
  ring
end Lean4LPD.LayerCounterexample
