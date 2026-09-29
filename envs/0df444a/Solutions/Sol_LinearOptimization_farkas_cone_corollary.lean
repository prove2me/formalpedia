-- Prove2me | solution 1 for LinearOptimization.farkas_cone_corollary
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:54:58.898254+00:00
-- url     : https://prove2.me/submissions/19f5b071-ddbb-442b-b3fc-7413851c6148

import Theorems.Thm_LinearOptimization_farkas_lemma

open Matrix

theorem solution {m n : ℕ} (A : Fin n → (Fin m → ℝ))
    (b : Fin m → ℝ)
    (h : ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p ⬝ᵥ A i) → 0 ≤ p ⬝ᵥ b) :
    ∃ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) ∧ b = ∑ i, lam i • A i := by
  classical
  let M : Matrix (Fin m) (Fin n) ℝ := fun i j ↦ A j i
  rcases LinearOptimization.farkas_lemma M b with hfirst | hsecond
  · rcases hfirst.1 with ⟨lam, hlam, hM⟩
    refine ⟨lam, hlam, ?_⟩
    rw [← hM]
    funext i
    simp [M, Matrix.mulVec, dotProduct, mul_comm]
  · rcases hsecond.1 with ⟨p, hp, hpb⟩
    have hpA : ∀ j, 0 ≤ p ⬝ᵥ A j := by
      intro j
      simpa [M, Matrix.mulVec_apply_eq_sum, Matrix.transpose, Matrix.of_apply, dotProduct, mul_comm] using hp j
    exact ((not_lt_of_ge (h p hpA)) hpb).elim
