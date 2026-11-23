-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:29:28.325186+00:00
-- url     : https://prove2.me/submissions/2da65e77-90d5-40a5-811f-7313e58a59ca

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (C : Set (ℝ × ℝ)) (hC : MeasurableSet C)
    (hfinite : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    MemLp (fun ω => (N.N ω C).toReal) 2 P := by
  have hcount : Measurable (fun ω => N.N ω C) := N.measurable_eval hC
  have hg : Measurable (fun x : ℝ≥0∞ => (x.toReal)^2) :=
    ENNReal.measurable_toReal.pow_const 2
  have hsq : Integrable (fun ω => ((N.N ω C).toReal)^2) P := by
    rw [show (fun ω => ((N.N ω C).toReal)^2) =
        (fun x : ℝ≥0∞ => (x.toReal)^2) ∘ (fun ω => N.N ω C) from rfl,
      ← integrable_map_measure hg.aestronglyMeasurable hcount.aemeasurable,
      N.poisson_law hC hfinite]
    change Integrable (fun x : ℝ≥0∞ => (x.toReal)^2)
      ((poissonMeasure (LevyStochCalc.Poisson.referenceIntensity ν C).toNNReal).map
        (fun n : ℕ => (n : ℝ≥0∞)))
    rw [integrable_map_measure hg.aestronglyMeasurable
        measurable_from_nat.aemeasurable]
    simpa [Function.comp_def] using LevyStochCalc.Probability.integrable_pow_poissonMeasure
      (LevyStochCalc.Poisson.referenceIntensity ν C).toNNReal 2
  exact (memLp_two_iff_integrable_sq
    (ENNReal.measurable_toReal.comp hcount).aestronglyMeasurable).2 hsq
