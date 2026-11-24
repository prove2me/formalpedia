-- Prove2me | solution 1 for GlobalTheory.levi_element_cpx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:58.275894+00:00
-- url     : https://prove2.me/submissions/dae44c1b-b517-4e0e-8b28-1b9c0f2282d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  intro n a b J Q hJ hQ X₁ Y₁ Xb Yb h11 h1b hbb h1Y h1Yb hYbYb hbYb

  have hYb1 : Ybᴴ * J * X₁ = 0 := by
    have := congrArg conjTranspose h1Yb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hYbb : Ybᴴ * J * Xb = 1 := by
    have := congrArg conjTranspose hbYb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hY1 : Y₁ᴴ * J * X₁ = 1 := by
    have := congrArg conjTranspose h1Y
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this

  have hinj : Function.Injective X₁.mulVec := by
    intro x y hxy
    have := congrArg (fun w => (Y₁ᴴ * J) *ᵥ w) hxy
    simp only [mulVec_mulVec] at this
    simpa [hY1] using this
  set G := X₁ᴴ * Q * X₁ with hG
  have hGpd : G.PosDef := hQ.conjTranspose_mul_mul_same hinj
  have hGu : IsUnit G := hGpd.isUnit
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  set A : Matrix (Fin a) (Fin b) ℂ := -(G⁻¹ * (X₁ᴴ * Q * Xb)) with hA
  set T : Matrix (Fin n) (Fin n) ℂ := X₁ * A * Ybᴴ * J - Yb * Aᴴ * X₁ᴴ * J with hT
  have hT2 : T * T = 0 := by
    simp only [hT, sub_mul, mul_sub]
    have e1 : X₁ * A * Ybᴴ * J * (X₁ * A * Ybᴴ * J) = X₁ * A * (Ybᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e2 : X₁ * A * Ybᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = X₁ * A * (Ybᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e3 : Yb * Aᴴ * X₁ᴴ * J * (X₁ * A * Ybᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e4 : Yb * Aᴴ * X₁ᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2, e3, e4, hYb1, hYbYb, h11, h1Yb]
    simp
  have hTJ : Tᴴ * J = -(J * T) := by
    simp only [hT, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJ, sub_mul, mul_sub,
      Matrix.mul_assoc, neg_sub]
  let u : GL (Fin n) ℂ := ⟨1 + T, 1 - T, by
      rw [mul_sub, mul_one, add_mul, one_mul, hT2]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hT2]; abel⟩
  refine ⟨u, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 + T)ᴴ * J * (1 + T) = J
    rw [conjTranspose_add, conjTranspose_one, add_mul, one_mul, add_mul, mul_add, mul_add, hTJ]
    simp only [mul_one, neg_mul, Matrix.mul_assoc, hT2, mul_zero, neg_zero, add_zero]
    abel
  · show (1 + T) * X₁ = X₁
    have : T * X₁ = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * X₁ = X₁ * A * (Ybᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * X₁ = Yb * Aᴴ * (X₁ᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYb1, h11]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · show (1 + T) * Xb = Xb + X₁ * A
    have : T * Xb = X₁ * A := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Xb = X₁ * A * (Ybᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Xb = Yb * Aᴴ * (X₁ᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbb, h1b]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this]
  · show (1 + T) * Yb = Yb
    have : T * Yb = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Yb = X₁ * A * (Ybᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Yb = Yb * Aᴴ * (X₁ᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbYb, h1Yb]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · intro v hv
    show (1 + T) *ᵥ v = v + X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v))
    rw [add_mulVec, one_mulVec]
    congr 1
    simp only [hT, sub_mulVec]
    have e1 : (X₁ * A * Ybᴴ * J) *ᵥ v = X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (Yb * Aᴴ * X₁ᴴ * J) *ᵥ v = (Yb * Aᴴ) *ᵥ ((X₁ᴴ * J) *ᵥ v) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [e1, e2, hv, mulVec_zero, sub_zero]
  · rw [Matrix.mul_add]
    have : X₁ᴴ * Q * (X₁ * A) = G * A := by rw [hG]; simp only [Matrix.mul_assoc]
    rw [this, hA, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mul]
    simp
end GlobalTheory
