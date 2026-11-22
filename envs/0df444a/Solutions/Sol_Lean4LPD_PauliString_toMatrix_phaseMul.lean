-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_phaseMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:50.433772+00:00
-- url     : https://prove2.me/submissions/0ad057cc-d57d-48eb-b8cb-15aa35a0620b

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_iPow_add
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_star_negOnePow
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self


attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.star_negOnePow
attribute [local simp] Lean4LPD.PauliString.toMatrix_one

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (k : ZMod 4) (s : PauliString n) :
    toMatrix (phaseMul k s) = iPow k • toMatrix s := by
  ext a b
  rw [toMatrix_apply, Matrix.smul_apply, toMatrix_apply, phaseMul_x, phaseMul_z, phaseMul_phase]
  by_cases h : a = b + s.x
  · rw [if_pos h, if_pos h, iPow_add, smul_eq_mul]
    ring
  · rw [if_neg h, if_neg h, smul_zero]
end Lean4LPD.PauliString
