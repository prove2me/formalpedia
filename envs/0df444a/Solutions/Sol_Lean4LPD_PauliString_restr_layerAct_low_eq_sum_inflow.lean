-- Prove2me | solution 1 for Lean4LPD.PauliString.restr_layerAct_low_eq_sum_inflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:45.188859+00:00
-- url     : https://prove2.me/submissions/20f2e701-f132-4c28-94bc-96717627ec5a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_layerAct_eq_sum_layerJump
public import Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_mulVec
public import Theorems.Thm_Lean4LPD_PauliString_restr_sum

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ)) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    restr (highSet n w) (layerAct L (restr (highSet n w)ᶜ y))
      = ∑ j ∈ range (L.length + 1), Lean4LPD.clm (layerInflowMatrix L w j) y := by
  rw [layerAct_eq_sum_layerJump, restr_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (layerInflowMatrix_mulVec L w j y).symm
end Lean4LPD.PauliString
