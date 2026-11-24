-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionRealCountSecondMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:31.360679+00:00
-- url     : https://prove2.me/submissions/7736b61d-3a22-40e0-92f3-50760de863b9

import Theorems.Thm_Kyprianou_Ch02_poissonMeasureRealSecondMomentV1
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    (∫ ω, ((N.N ω R).toReal) ^ 2 ∂P) =
      (LevyStochCalc.Poisson.referenceIntensity ν R).toReal ^ 2 +
        (LevyStochCalc.Poisson.referenceIntensity ν R).toReal := by
  have hg : Measurable (fun x : ℝ≥0∞ => x.toReal ^ 2) :=
    ENNReal.measurable_toReal.pow_const 2
  have hc : Measurable (fun ω => N.N ω R) := N.measurable_eval hR
  rw [← integral_map hc.aemeasurable hg.aestronglyMeasurable,
    N.poisson_law hR hfinite]
  unfold LevyStochCalc.Poisson.poissonMeasureENN
  rw [integral_map measurable_from_nat.aemeasurable hg.aestronglyMeasurable]
  simpa only [ENNReal.toReal_natCast, ENNReal.coe_toNNReal_eq_toReal] using Kyprianou.Ch02.poissonMeasureRealSecondMomentV1
    (LevyStochCalc.Poisson.referenceIntensity ν R).toNNReal
