-- Prove2me | solution 1 for Kyprianou.Ch04.physicalAbsoluteLedgerMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:11:45.465085+00:00
-- url     : https://prove2.me/submissions/36c86d3e-a968-4185-9c83-6a46cd672143

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The absolute physical mark integral is a measurable nonnegative random variable,
with no moment requirement on the mark law. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    Measurable (fun w => ∫ z in D, |z.2| ∂(N.N w)) := by
  let R : Ω → Measure (ℝ × ℝ) := fun w => (N.N w).restrict D
  have hR : Measurable R := Measure.measurable_of_measurable_coe R fun s hs => by
    simpa only [R,Measure.restrict_apply hs] using N.measurable_eval (hs.inter hD)
  have hg : Measurable (fun z : ℝ × ℝ => |z.2|) := measurable_snd.abs
  have hm := (Measure.measurable_lintegral
    (ENNReal.measurable_ofReal.comp hg)).comp hR
  have he (w : Ω) : (∫ z in D, |z.2| ∂(N.N w)) =
      (∫⁻ z, ENNReal.ofReal |z.2| ∂(R w)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => abs_nonneg z.2)
      hg.aestronglyMeasurable
  simp_rw [he]
  exact ENNReal.measurable_toReal.comp hm
