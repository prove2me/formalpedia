-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_finset_weighted_square_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:37:32.032191+00:00
-- url     : https://prove2.me/submissions/526fcfb8-5a8f-4a03-8bec-d38809bb1a1c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-- The integral of a finite squared weighted sum is the double sum of moments. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (F : Finset ι) (X : ι → Ω → ℝ)
    (a : ι → ℝ)
    (hprod : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => X i ω * X j ω) P) :
    (∫ ω, (∑ i ∈ F, a i * X i ω) ^ 2 ∂P) =
      ∑ i ∈ F, ∑ j ∈ F, (a i * a j) *
        (∫ ω, X i ω * X j ω ∂P) := by
  have hpair : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => (a i * a j) * (X i ω * X j ω)) P := by
    intro i hi j hj
    exact (hprod i hi j hj).const_mul _
  have hinner : ∀ i ∈ F, Integrable
      (fun ω => ∑ j ∈ F, (a i * a j) * (X i ω * X j ω)) P := by
    intro i hi
    exact integrable_finset_sum F (hpair i hi)
  have hpoint : ∀ ω, (∑ i ∈ F, a i * X i ω) ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, (a i * a j) * (X i ω * X j ω) := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ ω, (∑ i ∈ F, a i * X i ω) ^ 2 ∂P) =
        (∫ ω, ∑ i ∈ F, ∑ j ∈ F,
          (a i * a j) * (X i ω * X j ω) ∂P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ i ∈ F, (∫ ω, ∑ j ∈ F,
        (a i * a j) * (X i ω * X j ω) ∂P) :=
      integral_finset_sum F hinner
    _ = ∑ i ∈ F, ∑ j ∈ F,
        (∫ ω, (a i * a j) * (X i ω * X j ω) ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finset_sum F (hpair i hi)
    _ = ∑ i ∈ F, ∑ j ∈ F, (a i * a j) *
        (∫ ω, X i ω * X j ω ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
