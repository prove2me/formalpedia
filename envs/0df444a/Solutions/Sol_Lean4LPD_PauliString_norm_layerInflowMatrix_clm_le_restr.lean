-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le_restr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:57:50.999518+00:00
-- url     : https://prove2.me/submissions/fa5795bf-24c7-45f8-8ab3-1446eacbfce5

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_clm_restr
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_clm_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ)) {kh w w' j : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (hw : w' + j * (kh - 1) ≤ w)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ))
        * ‖restr (highSet n w') y‖ := by
  rw [layerInflowMatrix_clm_restr L (fun g hg => hL.weight_le g.1 (List.mem_map_of_mem hg)) hw]
  exact norm_layerInflowMatrix_clm_le L hL hσ hsin w j _
end Lean4LPD.PauliString
