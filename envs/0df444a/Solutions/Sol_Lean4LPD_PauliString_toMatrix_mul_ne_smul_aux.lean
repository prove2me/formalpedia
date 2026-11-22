-- Prove2me | solution 1 for Lean4LPD.PauliString.toMatrix_mul_ne_smul_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:31.621534+00:00
-- url     : https://prove2.me/submissions/7797b511-6b3e-4dbb-bcf1-67140ea6decc

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
public import Theorems.Thm_Lean4LPD_negOnePow_eq_one_iff
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_star_negOnePow
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_add
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul_toMatrix_inv
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero
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
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
section
@[expose] public section
namespace Lean4LPD
namespace PauliString
variable {n : ℕ} {G s t : PauliString n}
private lemma dotProduct_eq_zero_of_forall {u : Bits n} (h : ∀ b : Bits n, u ⬝ᵥ b = 0) : u = 0 := by
  funext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single, mul_one] at this
private lemma x_and_z_eq_zero_of_toMatrix_eq_smul_one {c : ℂ}
    (h : toMatrix G = c • (1 : Matrix (Bits n) (Bits n) ℂ)) :
    G.x = 0 ∧ G.z = 0 := by
  have key : ∀ a b : Bits n, toMatrix G a b = c * (if a = b then 1 else 0) := by
    intro a b
    rw [h, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hx : G.x = 0 := by
    by_contra hne
    have h0 := key (0 + G.x) 0
    rw [toMatrix_apply_add] at h0
    rw [if_neg (by simpa using hne), mul_zero] at h0
    exact (mul_ne_zero (iPow_ne_zero _) (negOnePow_ne_zero _)) h0
  have hc : c = iPow G.phase := by
    have h0 := key (0 + G.x) 0
    rw [toMatrix_apply_add, if_pos (by simp [hx]), mul_one] at h0
    simpa using h0.symm
  refine ⟨hx, ?_⟩
  refine dotProduct_eq_zero_of_forall (fun b => ?_)
  have h0 := key (b + G.x) b
  rw [toMatrix_apply_add, if_pos (by simp [hx]), mul_one, hc] at h0
  exact negOnePow_eq_one_iff.1 (mul_left_cancel₀ (iPow_ne_zero G.phase) (by rw [h0, mul_one]))
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
theorem _root_.solution (h : sympForm G s = 1) (c : ℂ) :
    toMatrix (G * s) ≠ c • toMatrix s := by
  intro heq
  rw [← toMatrix_mul] at heq
  have hG : toMatrix G = c • (1 : Matrix (Bits n) (Bits n) ℂ) := by
    have := congrArg (· * toMatrix s⁻¹) heq
    simp only [smul_mul_assoc, mul_assoc, toMatrix_mul_toMatrix_inv, mul_one] at this
    exact this
  obtain ⟨hx, hz⟩ := x_and_z_eq_zero_of_toMatrix_eq_smul_one hG
  rw [sympForm_eq_zero_of_x_eq_zero_of_z_eq_zero hx hz] at h
  exact absurd h (by decide)
end Lean4LPD.PauliString
