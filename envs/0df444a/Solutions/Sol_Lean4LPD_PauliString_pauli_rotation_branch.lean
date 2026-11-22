-- Prove2me | solution 1 for Lean4LPD.PauliString.pauli_rotation_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:33.688801+00:00
-- url     : https://prove2.me/submissions/a09ecfa1-c08f-45bf-b31c-a5d422984c8f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_or_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_anticommute
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_commute
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_self_of_isSelfAdjoint
public import Theorems.Thm_Lean4LPD_rot_conj_of_commute


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hG : IsSelfAdjoint G) (s : PauliString n) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = if sympForm G s = 0 then toMatrix s
        else (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s) := by
  have hG2 : toMatrix G * toMatrix G = 1 := toMatrix_mul_self_of_isSelfAdjoint hG
  rcases sympForm_eq_zero_or_one G s with h | h
  · rw [if_pos h]
    exact rot_conj_of_commute hG2 (toMatrix_commute h)
  · have hne : ¬ sympForm G s = 0 := by rw [h]; decide
    rw [if_neg hne, rot_conj_of_anticommute hG2 (toMatrix_anticommute h), toMatrix_mul]
end Lean4LPD.PauliString
