-- Prove2me | solution 1 for Lean4LPD.PauliString.norm_layerInflowMatrix_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:54:13.172974+00:00
-- url     : https://prove2.me/submissions/a830c6f2-6273-4a50-80a2-93e7cfb9d807

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
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
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ (((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ) := by
  calc ‖layerInflowMatrix L w j‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j :=
        norm_layerInflowMatrix_le L hL hσ hsin w j
    _ ≤ (((w + j * (kh - 1) : ℕ) : ℝ) ^ j / (Nat.factorial j : ℝ)) * σ ^ j :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j (w + j * (kh - 1)))
          (pow_nonneg hσ j)
    _ = _ := by rw [mul_pow]; ring
end Lean4LPD.PauliString
