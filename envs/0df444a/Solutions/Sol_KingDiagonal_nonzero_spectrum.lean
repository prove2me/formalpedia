-- Prove2me | solution 1 for KingDiagonal.nonzero_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:23:00.493825+00:00
-- url     : https://prove2.me/submissions/4e0c5890-5761-4e50-bd08-ded68c634004

import Mathlib

open scoped Matrix
open Polynomial

theorem solution {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (X : Matrix a b ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  classical
  have hA : IsSelfAdjoint (Xᴴ * X) := Matrix.isHermitian_conjTranspose_mul_self X
  have hB : IsSelfAdjoint (X * Xᴴ) := Matrix.isHermitian_mul_conjTranspose_self X
  set s : Finset ℝ := (Matrix.finite_real_spectrum (A := Xᴴ * X)).toFinset ∪
    (Matrix.finite_real_spectrum (A := X * Xᴴ)).toFinset ∪ {0} with hs
  set p : ℝ[X] := Lagrange.interpolate s id f with hpdef
  have hp : ∀ x ∈ s, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
    exact this
  have h1 : cfc f (Xᴴ * X) = aeval (Xᴴ * X) p := by
    rw [← cfc_polynomial p (Xᴴ * X) hA]
    apply cfc_congr
    intro x hx
    exact (hp x (by simp [hs, hx])).symm
  have h2 : cfc f (X * Xᴴ) = aeval (X * Xᴴ) p := by
    rw [← cfc_polynomial p (X * Xᴴ) hB]
    apply cfc_congr
    intro x hx
    exact (hp x (by simp [hs, hx])).symm
  have hp0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [hs])]
    exact hf
  have hpow : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  have htr : ∀ k : ℕ, ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
    intro k
    rw [hpow, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]
  rw [h1, h2, aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases k with _ | k
  · simp [hp0]
  · rw [htr]
