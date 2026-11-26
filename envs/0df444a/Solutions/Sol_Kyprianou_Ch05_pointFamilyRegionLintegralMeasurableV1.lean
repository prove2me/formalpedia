-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyRegionLintegralMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:19:38.489714+00:00
-- url     : https://prove2.me/submissions/17056e16-f9b5-48e8-9e65-a88add9de4d7

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyAllRegionEvalMeasurableV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (R : Set E) (hR : MeasurableSet R) (g : E → ENNReal) (hg : Measurable g) :
    Measurable[prmEvalSigma K Z m R] (fun w => ∫⁻ z in R, g z ∂(poissonRandomMeasure K Z w)) := by
  have hM : Measurable[prmEvalSigma K Z m R]
      (fun w => (poissonRandomMeasure K Z w).restrict R) := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    simp only [Measure.restrict_apply hC]
    exact pointFamilyAllRegionEvalMeasurableV1 m K Z R (C ∩ R)
      (hC.inter hR) inter_subset_right
  exact (Measure.measurable_lintegral hg).comp hM
