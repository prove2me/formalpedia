-- Prove2me | solution 1 for LocalDistanceNetwork.moore_penrose_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:58:53.251855+00:00
-- url     : https://prove2.me/submissions/e5eb9d50-9440-4e65-b4fd-7db48b284ebd

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix
open LocalDistanceNetwork

namespace LDMP

lemma ht {m k : Type*} (N : Matrix m k ℝ) : Nᴴ = Nᵀ := conjTranspose_eq_transpose_of_trivial N

lemma eq_zero_of_tmul {m k : Type*} [Fintype m] (N : Matrix m k ℝ) (h : Nᵀ * N = 0) : N = 0 := by
  rw [← ht] at h; exact conjTranspose_mul_self_eq_zero.1 h

lemma unique {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℝ) (P Q : Matrix k m ℝ)
    (hP : IsMoorePenroseInverse M P) (hQ : IsMoorePenroseInverse M Q) : P = Q := by
  obtain ⟨p1, p2, p3, p4⟩ := hP
  obtain ⟨q1, q2, q3, q4⟩ := hQ
  have hP' : P = P * M * Q := by
    calc P = P * M * P := p2.symm
      _ = P * (M * P)ᵀ := by rw [p3, Matrix.mul_assoc]
      _ = P * Pᵀ * Mᵀ := by rw [transpose_mul, Matrix.mul_assoc]
      _ = P * Pᵀ * (M * Q * M)ᵀ := by rw [q1]
      _ = P * (M * P)ᵀ * (M * Q)ᵀ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = P * M * P * M * Q := by rw [p3, q3]; simp only [Matrix.mul_assoc]
      _ = P * M * Q := by rw [p2]
  have hQ' : Q = P * M * Q := by
    calc Q = Q * M * Q := q2.symm
      _ = (Q * M)ᵀ * Q := by rw [q4]
      _ = Mᵀ * Qᵀ * Q := by rw [transpose_mul]
      _ = (M * P * M)ᵀ * Qᵀ * Q := by rw [p1]
      _ = (P * M)ᵀ * (Q * M)ᵀ * Q := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = P * M * Q * M * Q := by rw [p4, q4]; simp only [Matrix.mul_assoc]
      _ = P * M * Q := by
          rw [show P * M * Q * M * Q = P * M * (Q * M * Q) by simp only [Matrix.mul_assoc], q2]
  rw [hP', ← hQ']

lemma exists_mp {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℝ) :
    ∃ P : Matrix k m ℝ, IsMoorePenroseInverse M P := by
  classical
  have hA : (Mᵀ * M).IsHermitian := by
    have := isHermitian_conjTranspose_mul_self M; rwa [ht] at this
  set U : Matrix k k ℝ := (hA.eigenvectorUnitary : Matrix k k ℝ)
  set ev := hA.eigenvalues
  have hspec : Mᵀ * M = U * diagonal ev * Uᵀ := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    have hd : (RCLike.ofReal ∘ hA.eigenvalues : k → ℝ) = ev := by funext i; simp [ev]
    rw [hd, Matrix.star_eq_conjTranspose, ht] at this
    exact this
  have hUU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, ht] at this
  have hUU' : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose, ht] at this
  set Ap : Matrix k k ℝ := U * diagonal (fun i => (ev i)⁻¹) * Uᵀ
  obtain ⟨A, hAdef⟩ : ∃ A, A = Mᵀ * M := ⟨_, rfl⟩
  rw [← hAdef] at hspec
  have hdd : diagonal ev * diagonal (fun i => (ev i)⁻¹) * diagonal ev = diagonal ev := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : ev i = 0
    · simp [h]
    · field_simp
  have hdd' : diagonal (fun i => (ev i)⁻¹) * diagonal ev * diagonal (fun i => (ev i)⁻¹)
      = diagonal (fun i => (ev i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : ev i = 0
    · simp [h]
    · field_simp
  have hcomm : diagonal ev * diagonal (fun i => (ev i)⁻¹) = diagonal (fun i => (ev i)⁻¹) * diagonal ev := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; ext i; ring
  have e3 : ∀ X Y Z : Matrix k k ℝ, U * X * Uᵀ * (U * Y * Uᵀ) * (U * Z * Uᵀ) = U * (X * Y * Z) * Uᵀ := by
    intro X Y Z
    calc U * X * Uᵀ * (U * Y * Uᵀ) * (U * Z * Uᵀ) = U * X * (Uᵀ * U) * Y * (Uᵀ * U) * Z * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have e2 : ∀ X Y : Matrix k k ℝ, U * X * Uᵀ * (U * Y * Uᵀ) = U * (X * Y) * Uᵀ := by
    intro X Y
    calc U * X * Uᵀ * (U * Y * Uᵀ) = U * X * (Uᵀ * U) * Y * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hAAA : A * Ap * A = A := by rw [hspec, e3, hdd]
  have hApAAp : Ap * A * Ap = Ap := by rw [hspec, e3, hdd']
  have hApA : Ap * A = A * Ap := by rw [hspec, e2, e2, hcomm]
  have hApT : Apᵀ = Ap := by
    simp only [Ap, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hAT : Aᵀ = A := by simp [hAdef, transpose_mul]
  -- M * Ap * A = M
  have hMQ : M * (1 - Ap * A) = 0 := by
    apply eq_zero_of_tmul
    have hQT : (1 - Ap * A)ᵀ = 1 - Ap * A := by
      rw [transpose_sub, transpose_one, transpose_mul, hApT, hAT, hApA]
    rw [transpose_mul, hQT, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, ← hAdef,
      Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hApA, hAAA, sub_self, Matrix.mul_zero]
  have hM : M * Ap * A = M := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hMQ
    rw [Matrix.mul_assoc, ← hMQ]
  refine ⟨Ap * Mᵀ, ?_, ?_, ?_, ?_⟩
  · rw [show M * (Ap * Mᵀ) * M = M * Ap * (Mᵀ * M) by simp only [Matrix.mul_assoc], ← hAdef, hM]
  · rw [show Ap * Mᵀ * M * (Ap * Mᵀ) = Ap * (Mᵀ * M) * Ap * Mᵀ by simp only [Matrix.mul_assoc],
      ← hAdef, hApAAp]
  · rw [transpose_mul, transpose_mul, transpose_transpose, hApT, Matrix.mul_assoc]
  · rw [show Ap * Mᵀ * M = Ap * (Mᵀ * M) by simp only [Matrix.mul_assoc], ← hAdef, transpose_mul,
      hAT, hApT, hApA]

end LDMP

theorem solution {m k : Type*} [Fintype m] [Fintype k]
    (M : Matrix m k ℝ) :
    ∃! P : Matrix k m ℝ, IsMoorePenroseInverse M P := by
  obtain ⟨P, hP⟩ := LDMP.exists_mp M
  exact ⟨P, hP, fun Q hQ => LDMP.unique M Q P hQ hP⟩
