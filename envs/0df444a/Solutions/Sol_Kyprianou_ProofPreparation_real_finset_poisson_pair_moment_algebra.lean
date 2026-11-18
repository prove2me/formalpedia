-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_finset_poisson_pair_moment_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:38:09.276202+00:00
-- url     : https://prove2.me/submissions/f4990437-da4d-41a1-96aa-056e490d4928

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

/-- Sum a Poisson pair-moment kernel into squared mean and variance. -/
theorem solution
    {ι : Type} [DecidableEq ι] (F : Finset ι)
    (a r : ι → ℝ) :
    (∑ i ∈ F, ∑ j ∈ F,
      (a i * a j) * (r i * r j + if i = j then r i else 0)) =
      (∑ i ∈ F, a i * r i) ^ 2 +
      ∑ i ∈ F, a i ^ 2 * r i := by
  have hpair : ∀ i ∈ F, ∀ j ∈ F,
      (a i * a j) * (r i * r j + if i = j then r i else 0) =
        (a i * r i) * (a j * r j) +
        if i = j then a i ^ 2 * r i else 0 := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
      ring
  calc
    (∑ i ∈ F, ∑ j ∈ F,
      (a i * a j) * (r i * r j + if i = j then r i else 0)) =
        ∑ i ∈ F, ∑ j ∈ F,
          ((a i * r i) * (a j * r j) +
            if i = j then a i ^ 2 * r i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair i hi j hj
    _ = (∑ i ∈ F, ∑ j ∈ F, (a i * r i) * (a j * r j)) +
        ∑ i ∈ F, ∑ j ∈ F, if i = j then a i ^ 2 * r i else 0 := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i ∈ F, a i * r i) ^ 2 +
        ∑ i ∈ F, a i ^ 2 * r i := by
      rw [← Finset.sum_mul_sum, ← pow_two]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.sum_ite_eq', hi]
