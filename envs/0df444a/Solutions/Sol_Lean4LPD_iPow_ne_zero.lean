-- Prove2me | solution 1 for Lean4LPD.iPow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:24.833802+00:00
-- url     : https://prove2.me/submissions/279c43d7-663c-4a7f-9ba5-cbdc6fcdff7d

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_iPow_three
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
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
section
@[expose] public section
namespace Lean4LPD
private lemma zmod_four_cases (k : ZMod 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide
namespace PauliString
variable {n : ℕ} {G s t : PauliString n}
example : toMatrix X1 0 0 = 0 ∧ toMatrix X1 0 1 = 1 ∧
    toMatrix X1 1 0 = 1 ∧ toMatrix X1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 0 + X1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 1 + X1.x)]; simp [X1, negOnePow]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 0 + X1.x)]; simp [X1, negOnePow]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 1 + X1.x))]
example : toMatrix Z1 0 0 = 1 ∧ toMatrix Z1 0 1 = 0 ∧
    toMatrix Z1 1 0 = 0 ∧ toMatrix Z1 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 0 + Z1.x)]; simp [Z1, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 1 + Z1.x))]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 0 + Z1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 1 + Z1.x)]; simp [Z1, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
example : toMatrix Y1 0 0 = 0 ∧ toMatrix Y1 0 1 = -Complex.I ∧
    toMatrix Y1 1 0 = Complex.I ∧ toMatrix Y1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((0 : Bits 1) = 0 + Y1.x))]
  · rw [toMatrix_apply, if_pos (by decide : (0 : Bits 1) = 1 + Y1.x)]
    simp [Y1, iPow_one, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_pos (by decide : (1 : Bits 1) = 0 + Y1.x)]
    simp [Y1, iPow_one, negOnePow, show (1 : ZMod 2).val = 1 from rfl]
  · rw [toMatrix_apply, if_neg (by decide : ¬ ((1 : Bits 1) = 1 + Y1.x))]
end PauliString
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution (k : ZMod 4) : iPow k ≠ 0 := by
  rcases zmod_four_cases k with rfl | rfl | rfl | rfl <;>
    simp [iPow_one, iPow_three, Complex.I_ne_zero]
end Lean4LPD
