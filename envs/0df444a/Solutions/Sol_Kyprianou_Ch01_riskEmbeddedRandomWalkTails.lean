-- Prove2me | solution 1 for Kyprianou.Ch01.riskEmbeddedRandomWalkTails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:45:59.824617+00:00
-- url     : https://prove2.me/submissions/72310946-de42-4a93-bf72-279cb57807b3

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_Kyprianou_Ch01_riskEmbeddedPositiveTailSource
import Theorems.Thm_Kyprianou_Ch01_riskEmbeddedNegativeTailSource
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hClaims : F (Set.Iic (0 : ℝ)) = 0) :
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ :=
      (Ebeta.prod F).map
        (fun pair : ℝ × ℝ => pair.1 - pair.2)
    (∀ z : ℝ, 0 ≤ z →
      (mu (Set.Ioi z)).toReal =
        Real.exp (-beta * z) *
          (∫ u : ℝ, Real.exp (-beta * u) ∂F)) ∧
    (∀ z : ℝ, 0 < z →
      (mu (Set.Iio (-z))).toReal =
        (∫ e : ℝ, (F (Set.Ioi (e + z))).toReal ∂Ebeta)) := by
  exact ⟨Kyprianou.Ch01.riskEmbeddedPositiveTailSource beta hbeta F hClaims,
    Kyprianou.Ch01.riskEmbeddedNegativeTailSource beta hbeta F hClaims⟩
