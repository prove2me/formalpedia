-- Prove2me | solution 1 for MultiPeriod.measurableSet_feasGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:35.561201+00:00
-- url     : https://prove2.me/submissions/5f5f1933-18c1-4176-8ffa-34a94a629d0b

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_WeakP_measurable_toMeasure
import Theorems.Thm_MultiPeriod_measurable_projX
import Theorems.Thm_MultiPeriod_measurable_projY
import Theorems.Thm_measurableSet_eq_measure


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y)) (t : ℕ) :
    MeasurableSet (FeasGraph κμ κν t) := by
  have h1 : MeasurableSet {p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) |
      p.2.toMeasure.map Prod.fst = κμ t (projX t p.1)} := by
    refine measurableSet_eq_measure ?_ ?_ ?_ ?_
    · exact (Measure.measurable_map _ measurable_fst).comp
        (WeakP.measurable_toMeasure.comp measurable_snd)
    · exact (hκμ_meas t).comp ((measurable_projX t).comp measurable_fst)
    · intro p
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    · intro p
      exact hκμ_prob t _
  have h2 : MeasurableSet {p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) |
      p.2.toMeasure.map Prod.snd = κν t (projY t p.1)} := by
    refine measurableSet_eq_measure ?_ ?_ ?_ ?_
    · exact (Measure.measurable_map _ measurable_snd).comp
        (WeakP.measurable_toMeasure.comp measurable_snd)
    · exact (hκν_meas t).comp ((measurable_projY t).comp measurable_fst)
    · intro p
      exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    · intro p
      exact hκν_prob t _
  exact h1.inter h2
end MultiPeriod
