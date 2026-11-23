-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleCharFibreIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:20:47.300382+00:00
-- url     : https://prove2.me/submissions/ed7d6aa6-f400-48a1-ab9f-50ae97b446e7

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Integrate a finite-range complex characteristic integrand fibre by fibre. -/
theorem solution
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (ξ : ℝ) :
    (∫ x in B,
        (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν) =
      ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1)) := by
  classical
  let h : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1
  haveI : IsFiniteMeasure (ν.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hfinite
  have hm (x : ℝ) : MeasurableSet {y : ℝ | f y = x} :=
    (measurableSet_singleton x).preimage f.measurable
  have hrep : (fun y : ℝ => h (f y)) =
      (fun y : ℝ => ∑ x ∈ f.range,
        ({z : ℝ | f z = x}).indicator (fun _ => h x) y) := by
    funext y
    have hr : f y ∈ f.range :=
      SimpleFunc.mem_range.mpr ⟨y, rfl⟩
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    simp [hr]
  change (∫ y, h (f y) ∂(ν.restrict B)) =
    ∑ x ∈ f.range,
      (((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) * h x
  rw [hrep, integral_finset_sum f.range
      (fun x _ => (integrable_const (h x)).indicator (hm x))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [integral_indicator_const (h x) (hm x)]
  simp only [Measure.real_def]
  rw [Measure.restrict_apply (hm x), Set.inter_comm, Complex.real_smul]
