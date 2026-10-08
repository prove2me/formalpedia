-- Prove2me | solution 1 for Matrix.charpoly_roots_fin_two_of_trace_det
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T16:22:48.194508+00:00
-- url     : https://prove2.me/submissions/b994fa7b-73ed-4ac6-82e7-69c43a471da9

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

theorem solution {R : Type*} [CommRing R] [IsDomain R] {V : Matrix (Fin 2) (Fin 2) R} {μ₁ μ₂ : R}
    (htr : V.trace = μ₁ + μ₂) (hdet : V.det = μ₁ * μ₂) :
    V.charpoly.roots = {μ₁, μ₂} := by
  have h : V.charpoly = (X - C μ₁) * (X - C μ₂) := by
    rw [Matrix.charpoly_fin_two, htr, hdet]; simp only [C_add, C_mul]; ring
  rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl
