-- Prove2me | solution 1 for Lean4LPD.negOnePow_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:30.148012+00:00
-- url     : https://prove2.me/submissions/86eb6c1d-ea7c-492a-b76a-2147086c6e9f

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_negOnePow_add
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


attribute [local simp] Lean4LPD.negOnePow_zero
section
@[expose] public section
namespace Lean4LPD
private lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide
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
theorem _root_.solution (a : ZMod 2) : negOnePow a * negOnePow a = 1 := by
  rw [← negOnePow_add, zmod_two_add_self, negOnePow_zero]
end Lean4LPD
