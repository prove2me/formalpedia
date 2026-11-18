-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_finset_weighted_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:11:54.70773+00:00
-- url     : https://prove2.me/submissions/9fcc0a95-ca37-4e4d-bb6c-d1fc2c1ba6ab

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-- Pairwise product integrability gives integrability of finite weighted squares. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (F : Finset ι) (X : ι → Ω → ℝ)
    (a : ι → ℝ)
    (hprod : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => X i ω * X j ω) P) :
    Integrable (fun ω => (∑ i ∈ F, a i * X i ω) ^ 2) P := by
  have hp : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => (a i * a j) * (X i ω * X j ω)) P := by
    intro i hi j hj
    exact (hprod i hi j hj).const_mul _
  have hs : Integrable (fun ω => ∑ i ∈ F, ∑ j ∈ F,
      (a i * a j) * (X i ω * X j ω)) P := by
    apply integrable_finset_sum F
    intro i hi
    exact integrable_finset_sum F (hp i hi)
  have he : (fun ω => (∑ i ∈ F, a i * X i ω) ^ 2) =
      (fun ω => ∑ i ∈ F, ∑ j ∈ F,
        (a i * a j) * (X i ω * X j ω)) := by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact hs
