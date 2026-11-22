-- Prove2me | solution 1 for Lean4LPD.PauliString.pauli_rotation_branch_anticommute_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:46.884574+00:00
-- url     : https://prove2.me/submissions/b4b18d31-60b8-4b9e-bbcc-9d08a40a1c50

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_ne_smul
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_le_weight_add_kh
public import Theorems.Thm_Lean4LPD_PauliString_weight_sub_le_weight_mul


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G) (h : sympForm G s = 1)
    (hk : weight G ≤ kh) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
        = (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s)
      ∧ weight s - (kh - 1) ≤ weight (G * s)
      ∧ weight (G * s) ≤ weight s + (kh - 1)
      ∧ ∀ c : ℂ, toMatrix (G * s) ≠ c • toMatrix s :=
  ⟨pauli_rotation_branch_anticommute hG h θ,
   weight_sub_le_weight_mul hk h,
   weight_mul_le_weight_add_kh hk h,
   toMatrix_mul_ne_smul h⟩
end Lean4LPD.PauliString
