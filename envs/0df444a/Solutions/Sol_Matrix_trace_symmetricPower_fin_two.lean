-- Prove2me | solution 1 for Matrix.trace_symmetricPower_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:46:11.460888+00:00
-- url     : https://prove2.me/submissions/7ea61ca6-9a4d-49f1-b16a-5c1f99ff98d2

import Mathlib
import Definitions.Def_RPLib_S2_SymTrace

set_option autoImplicit false

open RamanujanPetersson.SymTrace in
theorem solution {R : Type} [CommRing R] (n : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hS : ∀ i j : Fin (n + 1), S i j =
      ((Polynomial.C (A 0 0) * Polynomial.X + Polynomial.C (A 1 0)) ^ (j : ℕ) *
        (Polynomial.C (A 0 1) * Polynomial.X + Polynomial.C (A 1 1)) ^ (n - (j : ℕ))).coeff (i : ℕ))
    (u : ℕ → R) (hu0 : u 0 = 1) (hu1 : u 1 = A.trace)
    (hu : ∀ k : ℕ, u (k + 2) = A.trace * u (k + 1) - A.det * u k) :
    S.trace = u n ∧
    (∀ x : R, A.trace = 2 * x → A.det = 1 → S.trace = (Polynomial.Chebyshev.U R (n : ℤ)).eval x) ∧
    (∀ α β : R, A.trace = α + β → A.det = α * β → ∀ m : ℕ,
      (S ^ m).trace = ∑ i ∈ Finset.range (n + 1), α ^ (m * i) * β ^ (m * (n - i))) := by
  have hSe : S = symMat n A := by
    ext i j
    rw [hS, symMat_apply]
  -- the recursion determines u
  have huU : ∀ k : ℕ, u k = U k A.trace A.det ∧ u (k + 1) = U (k + 1) A.trace A.det := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hu0], by simp [hu1]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [hu k, U_succ_succ, ih.1, ih.2]
  -- trace and determinant of powers of a 2 x 2 matrix
  have hpow : ∀ α β : R, A.trace = α + β → A.det = α * β → ∀ m : ℕ,
      (A ^ m).trace = α ^ m + β ^ m ∧ (A ^ m).det = α ^ m * β ^ m := by
    intro α β ht hd m
    refine ⟨?_, by rw [Matrix.det_pow, hd, mul_pow]⟩
    have hCH : A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
    have key : ∀ k : ℕ, (A ^ k).trace = α ^ k + β ^ k ∧
        (A ^ (k + 1)).trace = α ^ (k + 1) + β ^ (k + 1) := by
      intro k
      induction k with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [pow_zero, pow_zero, pow_zero, Matrix.trace_one, Fintype.card_fin]; norm_num
        · simp [ht]
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have e : A ^ (k + 1 + 1) = A.trace • A ^ (k + 1) - A.det • A ^ k := by
          rw [show k + 1 + 1 = k + 2 by ring, pow_add, hCH, Matrix.mul_sub, Matrix.mul_smul,
            Matrix.mul_smul, Matrix.mul_one, ← pow_succ]
        rw [e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2, ht, hd, smul_eq_mul,
          smul_eq_mul]
        ring
    exact (key m).1
  have h1 : S.trace = u n := by
    rw [hSe, trace_symMat, (huU n).1]
  refine ⟨h1, ?_, ?_⟩
  · intro x ht hd
    rw [h1, (huU n).1, ht, hd, U_two_mul_one]
  · intro α β ht hd m
    obtain ⟨tm, dm⟩ := hpow α β ht hd m
    rw [hSe, ← symMat_pow, trace_symMat, tm, dm, U_add_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_mul]
