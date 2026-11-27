-- Prove2me | solution 1 for GlobalTheory.TwistDual.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:32.956727+00:00
-- url     : https://prove2.me/submissions/6522538a-9602-4fa2-a00d-8dd87e49678e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FromColsMulVecEqZero
import Theorems.Thm_GlobalTheory_TwistDual_mulVec_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwistDual
open Matrix
variable {E : Type} [Field E] [StarRing E] [CharZero E]
namespace GlobalTheory.TwistDual
theorem _root_.solution {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hCC : Cᴴ * G * C = 0) (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    ∃ C' : Matrix (Fin n) (Fin r) E, Cᴴ * G * C' = 1 ∧ C'ᴴ * G * C' = 0 ∧ C'ᴴ * G * B = 0 := by
  have hs := mulVec_surjective hG hGd hC hBB hCB
  choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))
  set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i
  have key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a := by
    intro a k
    rw [← hv k]
    simp only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]
  have hC1 : Cᴴ * (G * C₁) = 1 := by
    ext j k
    have := key (Sum.inl j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢
    rw [this, Pi.single_apply, Matrix.one_apply]
    simp [eq_comm]
  have hB1 : Bᴴ * (G * C₁) = 0 := by
    ext j k
    have := key (Sum.inr j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢
    rw [this]
    simp
  have hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E),
      Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ := by
    intro p q X Y
    simp [conjTranspose_mul, hG, Matrix.mul_assoc]
  have hCC' : Cᴴ * (G * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCC
  have hCB' : Cᴴ * (G * B) = 0 := by rw [← Matrix.mul_assoc]; exact hCB
  have h1C : C₁ᴴ * (G * C) = 1 := by rw [hGc, hC1, conjTranspose_one]
  have h1B : C₁ᴴ * (G * B) = 0 := by
    have := congrArg conjTranspose hB1
    rw [conjTranspose_zero, ← hGc] at this
    exact this
  set S := C₁ᴴ * (G * C₁) with hSdef
  have hS : Sᴴ = S := by rw [hSdef, ← hGc]
  set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]
  have hXX : X + X = S := by
    rw [hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]
  have a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]
  refine ⟨C₁ - C * X, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]
    rw [← hSdef, ← hXX]; abel
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB',
      Matrix.mul_zero, sub_zero]
end GlobalTheory.TwistDual
