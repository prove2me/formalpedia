-- Prove2me | solution 1 for HodgeComputer.Formal.HoldoutCover.piola_contraction
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:21:41.393315+00:00
-- url     : https://prove2.me/submissions/dc2747cb-df21-472a-8609-b25f94dcfb0e

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

private lemma column_directional_aux {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z) (i : ι) (z : K) :
    ∑ j, M j i * E j z = D i z := by
  simp_rw [chain, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ k, (∑ j, M j i * (N k j * D k z)) = (N * M) k i * D k z := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hterm, hNM, Matrix.one_apply]
  simp

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K)
    (M N : Matrix ι ι K) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z) (u : ι → K) (f : K) :
    (∑ j, (∑ i, (u i / M.det) * M j i) * E j f) =
      (∑ i, u i * D i f) / M.det := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, column_directional_aux D E M N hNM chain]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring
