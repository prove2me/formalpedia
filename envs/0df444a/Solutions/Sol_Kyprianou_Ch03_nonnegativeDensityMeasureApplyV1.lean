-- Prove2me | solution 1 for Kyprianou.Ch03.nonnegativeDensityMeasureApplyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:07:51.887022+00:00
-- url     : https://prove2.me/submissions/dedf8f8b-a2ad-4903-96ec-79cf6d74878a

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f P) (hn : ∀ w, 0 ≤ f w)
    (A : Set Ω) (hA : MeasurableSet A) :
    (P.withDensity (fun w => ENNReal.ofReal (f w))) A =
      ENNReal.ofReal (∫ w, Set.indicator A f w ∂P) := by
  rw [withDensity_apply _ hA, integral_indicator hA]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall hn)).symm
