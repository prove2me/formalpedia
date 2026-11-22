-- Prove2me | solution 1 for Kyprianou.Ch01.boundedConvergenceExpectedUpper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:54:24.910493+00:00
-- url     : https://prove2.me/submissions/8a6f4488-e208-4504-8f07-99ca904e083d

import Mathlib
import Theorems.Thm_FamousTheorems_bounded_convergence

open MeasureTheory Filter
set_option autoImplicit false

/-- Uniform bounds transfer integral inequalities through pointwise limits. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (K C : ℝ)
    (hf : ∀ n, Measurable (f n))
    (hg : Measurable g)
    (hfBound : ∀ n ω, ‖f n ω‖ ≤ K)
    (hgBound : ∀ ω, ‖g ω‖ ≤ K)
    (hlim : ∀ ω, Filter.Tendsto (fun n => f n ω)
      Filter.atTop (nhds (g ω)))
    (hUpper : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable g P ∧ (∫ ω, g ω ∂P) ≤ C := by
  have hInt : Integrable g P :=
    Integrable.of_bound hg.aestronglyMeasurable K
      (Filter.Eventually.of_forall hgBound)
  have hT : Tendsto (fun n : ℕ => ∫ ω, f n ω ∂P)
      atTop (nhds (∫ ω, g ω ∂P)) :=
    FamousTheorems.bounded_convergence K
      (fun n => (hf n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (hfBound n))
      (Filter.Eventually.of_forall hlim)
  refine ⟨hInt, ?_⟩
  exact le_of_tendsto hT (Filter.Eventually.of_forall hUpper)
