-- Prove2me | solution 1 for GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:46.99129+00:00
-- url     : https://prove2.me/submissions/d8b33e6c-6399-4a06-b3d9-0c7501927073

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n E D hEE hEh hED hrank
  have h1 : E * (D.map σ)ᵀ = -(D * E) := eq_neg_of_add_eq_zero_left hED
  have h2 : E * (D.map σ)ᵀ = -(E * D * E) := by
    calc E * (D.map σ)ᵀ = E * (E * (D.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hEE]
      _ = E * (-(D * E)) := by rw [h1]
      _ = -(E * D * E) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hDE : D * E = E * D * E := by
    have := h1.symm.trans h2
    exact neg_inj.mp this
  have h3 : E * (D.map σ)ᵀ * E = -(E * D * E) := by
    rw [h2, Matrix.neg_mul, Matrix.mul_assoc (E * D) E E, hEE]
  have hV : E * (ε • (1 : Matrix (Fin n) (Fin n) k) - D) * E = ε • E - E * D * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE]
  refine ⟨E * (ε • 1 - D) * E, ?_, ?_⟩
  · rw [hV]
    have hm : ((ε • E - E * D * E).map σ)ᵀ = (σ ε) • (E.map σ)ᵀ - (E.map σ)ᵀ * (D.map σ)ᵀ * (E.map σ)ᵀ := by
      ext i j
      have hs : ((ε • E).map σ)ᵀ = σ ε • (E.map σ)ᵀ := by
        ext i j
        simp
      rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, ← Matrix.mul_assoc, hs]
    rw [hm, hEh, h3, hσε, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · have hM : E * (E * (ε • 1 - D) * E) + D = ε • E - E * D * E + D := by
      rw [hV, Matrix.mul_sub, Matrix.mul_smul, hEE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
    rw [hM]
    have hME : (ε • E - E * D * E + D) * E = ε • E := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hEE, Matrix.mul_assoc (E * D) E E, hEE, hDE]
      abel
    intro hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have haE : a ᵥ* E = 0 := by
      have : a ᵥ* ((ε • E - E * D * E + D) * E) = 0 := by rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      rw [hME, Matrix.vecMul_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hε
    have haD : a ᵥ* D = 0 := by
      have hx : a ᵥ* (E * D * E) = 0 := by
        rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, haE, Matrix.zero_vecMul]
      rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, haE, hx] at ha
      simpa using ha
    exact ha0 (hrank a haE haD)
end GlobalTheory
