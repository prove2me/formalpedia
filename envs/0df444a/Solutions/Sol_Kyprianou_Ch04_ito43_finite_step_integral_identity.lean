-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_finite_step_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:40.955646+00:00
-- url     : https://prove2.me/submissions/1bbe9e3f-cdb7-423d-9437-83aaa89c8680

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Distribute the finite sum against an integrable kernel, then restrict each measurable indicator set. -/
theorem solution
    {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (f : α → ℝ) (hf : IntegrableOn f S μ)
    (m : ℕ) (B : ℕ → Set α) (hB : ∀ i, MeasurableSet (B i)) (c : ℕ → ℝ) :
    let W : α → ℝ := fun x =>
      ∑ i ∈ Finset.range m, c i * (B i).indicator (fun _ => (1:ℝ)) x
    IntegrableOn (fun x => W x * f x) S μ ∧
      (∫ x in S, W x * f x ∂μ) =
        ∑ i ∈ Finset.range m, c i * (∫ x in B i ∩ S, f x ∂μ) := by
  classical
  dsimp only
  let F : ℕ → α → ℝ := fun i x => c i * (B i).indicator f x
  have hF (i : ℕ) : Integrable (F i) (μ.restrict S) :=
    (hf.indicator (hB i)).const_mul (c i)
  have heq : (fun x => (∑ i ∈ Finset.range m,
      c i * (B i).indicator (fun _ => (1:ℝ)) x) * f x) =
      fun x => ∑ i ∈ Finset.range m, F i x := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x ∈ B i <;> simp [F,Set.indicator,hx]
  rw [heq]
  constructor
  · exact integrable_finset_sum _ (fun i _ => hF i)
  · rw [integral_finset_sum _ (fun i _ => hF i)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [F,integral_const_mul,integral_indicator (hB i),
      Measure.restrict_restrict (hB i)]
