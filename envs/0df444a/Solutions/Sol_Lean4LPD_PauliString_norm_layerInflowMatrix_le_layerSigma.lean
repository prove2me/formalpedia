-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_layerInflowMatrix_le_layerSigma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:54:14.329028+00:00
-- url     : https://prove2.me/submissions/3c79d729-027f-44f0-b7d9-1075d15a7662

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_layerSigma_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_abs_sin_le_layerSigma
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * layerSigma L ^ j :=
  norm_layerInflowMatrix_le L hL (layerSigma_nonneg L) (abs_sin_le_layerSigma L) w j
end Lean4LPD.PauliString
