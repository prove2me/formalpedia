-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_restr_layerAct_le_sum_inflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:46.277134+00:00
-- url     : https://prove2.me/submissions/c3bc72b4-c55e-4c56-b1e7-43da8806520e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerAct
public import Theorems.Thm_Lean4LPD_PauliString_layerAct_add
public import Theorems.Thm_Lean4LPD_PauliString_restr_layerAct_low_eq_sum_inflow
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_le
public import Theorems.Thm_Lean4LPD_PauliString_restr_add
public import Theorems.Thm_Lean4LPD_PauliString_restr_add_restr_compl


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr (highSet n w) (layerAct L y)‖ ≤ ‖restr (highSet n w) y‖
      + ∑ j ∈ range (L.length + 1), ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖ := by
  have hsplit : restr (highSet n w) (layerAct L y)
      = restr (highSet n w) (layerAct L (restr (highSet n w) y))
        + restr (highSet n w) (layerAct L (restr (highSet n w)ᶜ y)) := by
    rw [← restr_add, ← layerAct_add, restr_add_restr_compl]
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_restr_le _ _).trans_eq (norm_layerAct L hL _)
  · rw [restr_layerAct_low_eq_sum_inflow]
    exact norm_sum_le _ _
end Lean4LPD.PauliString
