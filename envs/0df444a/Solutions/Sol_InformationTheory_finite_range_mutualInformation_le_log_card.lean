-- Prove2me | solution 1 for InformationTheory.finite_range_mutualInformation_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:57:24.197531+00:00
-- url     : https://prove2.me/submissions/6871689b-f818-4c79-be1b-42aeacf9ba63

import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
import Theorems.Thm_BanditAlgorithm_fin_probability_negMulLog_sum_le_log_card

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators

theorem _root_.solution
    {Omega Alpha : Type} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    (klDiv (Measure.map (fun x ↦ (f x, g x)) mu)
      ((Measure.map f mu).prod (Measure.map g mu))).toReal ≤ Real.log k := by
  let p : Fin k → ℝ := fun a ↦ (Measure.map g mu).real {a}
  letI : IsProbabilityMeasure (Measure.map g mu) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hp0 : ∀ a, 0 ≤ p a := fun a ↦ by positivity
  have hp1 : ∑ a, p a = 1 := by
    dsimp [p]
    rw [← Finset.sum_attach]
    simp
  exact (finite_range_mutualInformation_le_marginal_entropy mu f g hf hg).trans
    (BanditAlgorithm.fin_probability_negMulLog_sum_le_log_card p hp0 hp1)
