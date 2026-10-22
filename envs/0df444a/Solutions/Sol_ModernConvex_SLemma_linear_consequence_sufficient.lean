-- Prove2me | solution 1 for ModernConvex.SLemma.linear_consequence_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:01:48.727986+00:00
-- url     : https://prove2.me/submissions/76a31cdd-4a0e-49e0-9026-ea0281fe6ed9

import Mathlib

open Matrix

theorem solution {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (h : ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (B - ∑ i, lam i • A i).PosSemidef) :
    ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x ⬝ᵥ (A i *ᵥ x)) → 0 ≤ x ⬝ᵥ (B *ᵥ x) := by
  intro x hx
  obtain ⟨lam, hlam, hpsd⟩ := h
  have h1 := hpsd.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at h1
  rw [sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum] at h1
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 ≤ ∑ i, lam i * (x ⬝ᵥ (A i *ᵥ x)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (hx i)
  linarith
