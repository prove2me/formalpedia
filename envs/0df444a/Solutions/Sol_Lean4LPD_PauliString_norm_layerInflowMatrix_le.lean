-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_layerInflowMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:52.943901+00:00
-- url     : https://prove2.me/submissions/a4fb3008-9879-4225-a76b-c6f9b7d06d4d

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_row_sum_norm_layerInflowMatrix_le
public import Theorems.Thm_Lean4LPD_PauliString_col_sum_norm_layerInflowMatrix_le
public import Theorems.Thm_Lean4LPD_l2_opNorm_le_of_row_col_bound


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
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖ ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j := by
  apply Lean4LPD.l2_opNorm_le_of_row_col_bound _ (by positivity)
  · exact row_sum_norm_layerInflowMatrix_le L hL hσ hsin w j
  · intro q
    exact (col_sum_norm_layerInflowMatrix_le L hL hσ hsin w j q).trans
      (mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.choose_le_choose j (Nat.le_add_right w (j * (kh - 1))))
        (pow_nonneg hσ j))
end Lean4LPD.PauliString
