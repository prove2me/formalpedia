-- Prove2me | solution 1 for GlobalTheory.schur_complement_step_cpx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:44.965387+00:00
-- url     : https://prove2.me/submissions/b2102480-83a6-4f4a-895d-327a797d8732

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorization

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
theorem _root_.solution : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  intro n r J θ hJ hpos X Y hXY l d h u₁ A X₁ Xb X₂ Yb Y₂ hθ h0

  let K : Matrix (Fin (l + d)) (Fin d) ℂ := fun i j =>
    Fin.addCases (motive := fun _ => ℂ) (fun i => A i j)
      (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) i
  have hK : X₂ * K = Xb + X₁ * A := by
    ext a c
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp only [K, Fin.addCases_left, Fin.addCases_right, Matrix.add_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Matrix.mul_apply]
    rw [add_comm]
    rfl
  have hP : ∀ {m : ℕ} (f : Fin m → Fin (l + d)),
      (X₂.submatrix id f)ᴴ * (J * θ) * (Xb + X₁ * A)
        = (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix f id := fun _ => rfl
  have hrow1 : (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix (Fin.castAdd d) id = 0 :=
    (hP (Fin.castAdd d)).symm.trans h0
  have key : ∀ P : Matrix (Fin (l + d)) (Fin d) ℂ, P.submatrix (Fin.castAdd d) id = 0 →
      Y₂ * P = Yb * P.submatrix (Fin.natAdd l) id := by
    intro P hP0
    ext a c
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    have h00 : ∀ i, P (Fin.castAdd d i) c = 0 := fun i => by
      simpa using congrFun (congrFun hP0 i) c
    simp only [h00, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have hmain : θ * (Xb + X₁ * A) = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := by
    calc θ * (Xb + X₁ * A) = θ * X₂ * K := by rw [← hK, Matrix.mul_assoc]
      _ = u₁ * Y₂ * (X₂ᴴ * (J * θ) * X₂) * K := by rw [hθ]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (X₂ * K))) := by simp only [Matrix.mul_assoc]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [hK]
      _ = u₁ * (Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [key _ hrow1]; rfl
      _ = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := (Matrix.mul_assoc u₁ Yb _).symm
  have hzero : (X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) = 0 := by
    have h0' := h0
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at h0' ⊢
    rw [h0', Matrix.mul_zero]
  have hsame : Xbᴴ * (J * θ) * (Xb + X₁ * A)
      = (Xb + X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.add_mul, hzero, add_zero]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg Matrix.conjTranspose hXY
    simpa [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hL : (Ybᴴ * J) * (Xb + X₁ * A) = 1 := by
    have e1 : Ybᴴ * J * Xb = 1 := by
      have : Ybᴴ * J * Xb = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      simp [Matrix.one_apply, Fin.ext_iff]
    have e2 : Ybᴴ * J * X₁ = 0 := by
      have : Ybᴴ * J * X₁ = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin l => (⟨j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      have := j.isLt
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff, Matrix.zero_apply]
      rw [if_neg (by omega)]
    rw [Matrix.mul_add, e1, ← Matrix.mul_assoc, e2, Matrix.zero_mul, add_zero]
  have hinj : Function.Injective (Xb + X₁ * A).mulVec := by
    intro v w hvw
    have := congrArg (Ybᴴ * J).mulVec hvw
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.one_mulVec] at this
    exact this
  refine ⟨hmain, ?_⟩
  rw [hsame]
  exact hpos.conjTranspose_mul_mul_same hinj
end GlobalTheory
