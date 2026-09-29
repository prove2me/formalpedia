-- Prove2me | solution 1 for InformationTheory.categorical_toReal_klDiv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:05:35.671591+00:00
-- url     : https://prove2.me/submissions/fe8a2b21-1839-49bb-a825-547750aba54a

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators

namespace InformationTheory

theorem _root_.solution {k : ℕ} [NeZero k] (q p : Measure (Fin k))
    [IsProbabilityMeasure q] [IsProbabilityMeasure p] (hqp : q ≪ p) :
    (klDiv q p).toReal =
      ∑ a, q.real {a} * Real.log (q.real {a} / p.real {a}) := by
  rw [toReal_klDiv_of_measure_eq hqp (by simp)]
  rw [integral_fintype]
  · simp only [smul_eq_mul, llr]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hqa : q {a} = 0
    · simp [measureReal_def, hqa]
    have hpa : p {a} ≠ 0 := by
      intro h
      exact hqa (hqp h)
    have heq := congrArg (fun m : Measure (Fin k) ↦ m {a})
      (Measure.withDensity_rnDeriv_eq q p hqp)
    change (p.withDensity (q.rnDeriv p)) {a} = q {a} at heq
    rw [withDensity_apply _ (MeasurableSet.singleton a), lintegral_singleton] at heq
    have hrn : q.rnDeriv p a = q {a} / p {a} := by
      apply (ENNReal.eq_div_iff hpa (by finiteness)).2
      simpa [mul_comm] using heq
    rw [hrn]
    rw [ENNReal.toReal_div]
    simp only [measureReal_def]
  · exact Integrable.of_finite

end InformationTheory
