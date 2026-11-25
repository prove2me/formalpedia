-- Prove2me | solution 1 for Kyprianou.Ch04.simpleMarkIntensityFibresV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:38:07.168909+00:00
-- url     : https://prove2.me/submissions/c0402dc6-a96c-4cf4-ba6a-852a06e47bd8

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrating a simple mark is summing its intensity fibres. -/
theorem solution (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) :
    (∫ x in B, g x ∂ν) = ∑ r ∈ g.range, r * (ν (B ∩ g ⁻¹' {r})).toReal := by
  let A : ℝ → Set ℝ := fun r => B ∩ g ⁻¹' {r}
  have hA (r : ℝ) : MeasurableSet (A r) := hB.inter (g.measurableSet_fiber r)
  have hAs (r : ℝ) : A r ⊆ B := Set.inter_subset_left
  have hν_fin : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hfinite⟩
  have hg : ∀ x ∈ B, g x = ∑ r ∈ g.range, (A r).indicator (fun _ => r) x := by
    intro x hx
    rw [Finset.sum_eq_single (g x)]
    · rw [Set.indicator_of_mem (show x ∈ A (g x) from ⟨hx,rfl⟩)]
    · intro r _ hne
      exact Set.indicator_of_notMem (fun h => hne h.2.symm) _
    · intro hnot
      exact absurd (g.mem_range_self x) hnot
  have hgint : (∫ x in B, g x ∂ν) = ∑ r ∈ g.range, r * (ν (A r)).toReal := by
    rw [setIntegral_congr_fun hB hg, integral_finsetSum]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_indicator_const _ (hA r), Measure.real, Measure.restrict_apply (hA r),
        Set.inter_eq_left.mpr (hAs r), smul_eq_mul, mul_comm]
    · intro r _
      exact (integrable_const r).indicator (hA r)
  exact hgint
