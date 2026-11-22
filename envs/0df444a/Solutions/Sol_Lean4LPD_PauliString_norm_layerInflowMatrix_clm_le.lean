-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:56:04.44781+00:00
-- url     : https://prove2.me/submissions/7d124cb6-d7d7-414b-a4e2-a716f23ff3ba

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_le_factorial

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ)) * ‖y‖ := by
  apply (ContinuousLinearMap.le_opNorm _ y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  exact norm_layerInflowMatrix_le_factorial L hL hσ hsin w j
end Lean4LPD.PauliString
