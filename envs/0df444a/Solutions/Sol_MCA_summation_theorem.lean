-- Prove2me | solution 1 for MCA.summation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-06T18:23:48.919046+00:00
-- url     : https://prove2.me/submissions/63648e18-8563-474e-97d0-0c4436e0753c

import Mathlib

open scoped BigOperators
open Matrix

/-- The summation theorem for metabolic control analysis.

This is the deliverable that gets submitted to Prove2me. The target theorem is
`MCA.summation_theorem`; the server compares this declaration's type against
the target's formal statement.
-/
theorem solution
    {n m : ℕ}
    (e : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin 1) (Fin m) ℝ)
    (P : Matrix (Fin 1) (Fin n) ℝ)
    (T : Matrix (Fin 1) (Fin n) ℝ)
    (j : ℝ)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hA_left : Ainv * A = 1)
    (hA_right : A * Ainv = 1)
    (hF_chain : A * X + B = 0)
    (hJ_chain : T = R * X + P)
    (hF_hom : ∀ i, ∑ k, e k * B i k = 0)
    (hJ_hom : ∑ k, e k * P 0 k = j) :
    X = -Ainv * B ∧
      (∀ i, ∑ k, e k * X i k = 0) ∧
      T = -(R * Ainv) * B + P ∧
      (∑ k, e k * T 0 k = j) := by
  -- From AX + B = 0, isolate AX.
  have hAX : A * X = -B := by
    calc
      A * X = A * X + B - B := by abel
      _ = 0 - B := by rw [hF_chain]
      _ = -B := by simp

  -- Multiply AX = -B on the left by Ainv.
  have hX : X = -Ainv * B := by
    calc
      X = (Ainv * A) * X := by simp [hA_left]
      _ = Ainv * (A * X) := by rw [Matrix.mul_assoc]
      _ = Ainv * (-B) := by rw [hAX]
      _ = -Ainv * B := by rw [Matrix.mul_neg, Matrix.neg_mul]

  -- The rows of Ainv * B sum to zero against e.
  have hrow : ∀ i : Fin m, ∑ k, e k * (Ainv * B) i k = 0 := by
    intro i
    simp only [Matrix.mul_apply]
    calc
      ∑ k, e k * ∑ j, Ainv i j * B j k
          = ∑ k, ∑ j, e k * (Ainv i j * B j k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ k, e k * (Ainv i j * B j k) := by
            rw [Finset.sum_comm]
      _ = ∑ j, Ainv i j * ∑ k, e k * B j k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hF_hom j, mul_zero]

  -- Consequently the rows of X also sum to zero.
  have hXrow : ∀ i : Fin m, ∑ k, e k * X i k = 0 := by
    intro i
    rw [hX, Matrix.neg_mul]
    simp [hrow i]

  -- Substitute X into T.
  have hT : T = -(R * Ainv) * B + P := by
    rw [hJ_chain, hX]
    simp [Matrix.mul_assoc, neg_mul, mul_neg]

  -- The rows of (R * Ainv) * B sum to zero against e.
  have hRrow : ∑ k, e k * ((R * Ainv) * B) 0 k = 0 := by
    simp only [Matrix.mul_apply]
    calc
      ∑ k, e k * ∑ j, (R * Ainv) 0 j * B j k
          = ∑ k, ∑ j, e k * ((R * Ainv) 0 j * B j k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ k, e k * ((R * Ainv) 0 j * B j k) := by
            rw [Finset.sum_comm]
      _ = ∑ j, (R * Ainv) 0 j * ∑ k, e k * B j k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hF_hom j, mul_zero]

  have hB : ∑ k, e k * ((-(R * Ainv)) * B) 0 k = 0 := by
    rw [Matrix.neg_mul]
    simp [hRrow]

  -- Finally, evaluate the T-sum.
  have hTsum : ∑ k, e k * T 0 k = j := by
    rw [hT]
    simp [mul_add, Finset.sum_add_distrib, hB, hRrow, hJ_hom]

  exact ⟨hX, hXrow, hT, hTsum⟩
