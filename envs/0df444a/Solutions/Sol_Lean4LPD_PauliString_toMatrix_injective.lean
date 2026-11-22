-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:44.993629+00:00
-- url     : https://prove2.me/submissions/5e12ca2d-5566-43ab-9fc8-6ed28b0a1704

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_iPow_ne_zero
public import Theorems.Thm_Lean4LPD_negOnePow_ne_zero
public import Theorems.Thm_Lean4LPD_negOnePow_injective
public import Theorems.Thm_Lean4LPD_iPow_injective
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_star_negOnePow
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_add
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
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
public import Theorems.Thm_Lean4LPD_bits_add_eq_zero_iff
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
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
section
@[expose] public section
namespace Lean4LPD
private lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide
namespace PauliString
variable {n : ℕ} {G s t : PauliString n}
private lemma dotProduct_eq_zero_of_forall {u : Bits n} (h : ∀ b : Bits n, u ⬝ᵥ b = 0) : u = 0 := by
  funext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single, mul_one] at this
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
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution : Function.Injective (toMatrix (n := n)) := by
  intro s t hst
  have key : ∀ a b : Bits n, toMatrix s a b = toMatrix t a b := fun a b => by rw [hst]
  have hx : s.x = t.x := by
    have h0 := key (0 + s.x) 0
    rw [toMatrix_apply_add, toMatrix_apply] at h0
    by_cases hxx : 0 + s.x = 0 + t.x
    · simpa using hxx
    · rw [if_neg hxx] at h0
      exact absurd h0 (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _))
  have hp : s.phase = t.phase := by
    have h0 := key (0 + s.x) 0
    rw [toMatrix_apply_add, toMatrix_apply, if_pos (by rw [hx])] at h0
    simp only [dotProduct_zero, negOnePow_zero, mul_one] at h0
    exact iPow_injective h0
  have hz : s.z = t.z := by
    have hzz : ∀ b : Bits n, (s.z + t.z) ⬝ᵥ b = 0 := by
      intro b
      have h0 := key (b + s.x) b
      rw [toMatrix_apply_add, toMatrix_apply, if_pos (by rw [hx]), hp] at h0
      have := mul_left_cancel₀ (iPow_ne_zero t.phase) h0
      have hb : s.z ⬝ᵥ b = t.z ⬝ᵥ b := negOnePow_injective this
      rw [add_dotProduct, hb]
      exact zmod_two_add_self _
    have := dotProduct_eq_zero_of_forall hzz
    exact bits_add_eq_zero_iff.1 this
  exact ext' hx hz hp
end Lean4LPD.PauliString
