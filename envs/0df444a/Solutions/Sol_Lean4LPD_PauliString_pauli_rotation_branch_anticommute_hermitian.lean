-- Prove2me | solution 1 for Lean4LPD.PauliString.pauli_rotation_branch_anticommute_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:46.443249+00:00
-- url     : https://prove2.me/submissions/dac6d82a-2d26-448c-ab15-8647c778ccec

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G)
    (h : sympForm G s = 1) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = (Real.cos θ : ℂ) • toMatrix s
        + (Real.sin θ : ℂ) • toMatrix (phaseMul 1 (G * s)) := by
  rw [pauli_rotation_branch_anticommute hG h θ, toMatrix_phaseMul, iPow_one, smul_smul,
    mul_comm (Real.sin θ : ℂ) Complex.I]
end Lean4LPD.PauliString
