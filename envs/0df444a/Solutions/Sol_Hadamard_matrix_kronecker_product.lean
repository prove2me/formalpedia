-- Prove2me | solution 1 for Hadamard_matrix_kronecker_product
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-05T20:03:20.877581+00:00
-- url     : https://prove2.me/submissions/fb953fc8-8540-457b-96e6-abc4496f6039

import Mathlib

open Matrix

/-- Transport a `±1`-entried orthogonal matrix across an index equivalence. -/
private lemma transport_hadamard' {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (M : Matrix ι ι ℝ) (c : ℝ)
    (hpm : ∀ i j, M i j = 1 ∨ M i j = -1)
    (horth : M * Mᵀ = c • (1 : Matrix ι ι ℝ)) :
    (∀ i j, (M.submatrix e e) i j = 1 ∨ (M.submatrix e e) i j = -1) ∧
      (M.submatrix e e) * (M.submatrix e e)ᵀ = c • (1 : Matrix ι' ι' ℝ) := by
  refine ⟨fun i j => hpm (e i) (e j), ?_⟩
  apply Matrix.ext
  intro i j
  have hlhs : ((M.submatrix e e) * (M.submatrix e e)ᵀ) i j = (M * Mᵀ) (e i) (e j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun l => M (e i) l * M (e j) l)
  rw [hlhs, horth]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have hne : e i ≠ e j := fun heq => h (e.injective heq)
    simp [h, hne]

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hApm : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hAorth : A * Aᵀ = ((m : ℕ) : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (hBpm : ∀ i j, B i j = 1 ∨ B i j = -1)
    (hBorth : B * Bᵀ = ((n : ℕ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ M : Matrix (Fin (m * n)) (Fin (m * n)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((m * n : ℕ) : ℝ) • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) := by
  have hsmul_kron : ∀ (c c' : ℝ) (X : Matrix (Fin m) (Fin m) ℝ) (Y : Matrix (Fin n) (Fin n) ℝ),
      Matrix.kroneckerMap (· * ·) (c • X) (c' • Y) =
        (c * c') • Matrix.kroneckerMap (· * ·) X Y := by
    intro c c' X Y
    apply Matrix.ext
    intro i j
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set K : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ := Matrix.kroneckerMap (· * ·) A B with hKdef
  have hKpm : ∀ i j, K i j = 1 ∨ K i j = -1 := by
    intro i j
    rw [hKdef, Matrix.kroneckerMap_apply]
    rcases hApm i.1 j.1 with ha | ha <;> rcases hBpm i.2 j.2 with hb | hb <;>
      rw [ha, hb] <;> norm_num
  have hKorth : K * Kᵀ = (((m : ℕ) : ℝ) * (n : ℕ)) •
      (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ) := by
    rw [hKdef, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hAorth, hBorth,
        hsmul_kron, Matrix.one_kronecker_one]
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  obtain ⟨hfinal_pm, hfinal_orth⟩ := transport_hadamard' e.symm K (((m : ℕ) : ℝ) * (n : ℕ)) hKpm hKorth
  refine ⟨K.submatrix e.symm e.symm, hfinal_pm, ?_⟩
  have hcast : (((m : ℕ) : ℝ) * (n : ℕ)) = ((m * n : ℕ) : ℝ) := by push_cast; ring
  rwa [hcast] at hfinal_orth
