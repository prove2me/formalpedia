-- Prove2me | solution 1 for InfoGen.Gibbs.klDiv_dirac_eq
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:41:57.411376+00:00
-- url     : https://prove2.me/submissions/6695b347-d492-4aa9-8695-71ecff7dca58

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

theorem solution {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (Q : Measure W) [IsProbabilityMeasure Q] (w : W)
    (hQ : Q {w} ≠ 0) :
    klDiv (Measure.dirac w) Q =
      ENNReal.ofReal (-Real.log (Q {w}).toReal) := by
  have hac : Measure.dirac w ≪ Q := by
    intro s h0
    by_contra hne
    have hw : w ∈ s := by
      by_contra hw; exact hne (by rw [Measure.dirac_apply' _ (Set.to_countable s).measurableSet]; simp [hw])
    exact hQ (measure_mono_null (Set.singleton_subset_iff.mpr hw) h0)
  have hQt : Q {w} ≠ ⊤ := measure_ne_top _ _
  have hden : (Measure.dirac w).rnDeriv Q w = 1 / Q {w} := by
    have h := Measure.setLIntegral_rnDeriv hac ({w} : Set W)
    rw [lintegral_singleton, Measure.dirac_apply_of_mem (Set.mem_singleton w)] at h
    rw [← h, ENNReal.mul_div_cancel_right hQ hQt]
  have hmeas : ∀ f : W → ℝ, Measurable f := fun f => measurable_of_countable f
  have hint : Integrable (llr (Measure.dirac w) Q) (Measure.dirac w) :=
    (integrable_dirac (by simp))
  rw [klDiv_of_ac_of_integrable hac hint, integral_dirac]
  simp only [probReal_univ, add_sub_cancel_right, llr, hden]
  rw [ENNReal.toReal_div, ENNReal.toReal_one, one_div, Real.log_inv]
