-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPassageZeroDiscount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:45:29.654204+00:00
-- url     : https://prove2.me/submissions/4e736f0a-f9b3-46de-aa78-739421084f74

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    (∫ ω, passageLaplace (firstUpperPassage X s) (0 : ℝ) ω ∂P) = 1 := by
  exact (Kyprianou.Ch01.inverseGaussianZeroDiscountPositiveDrift
    P X b s hb hs hB hXmeas).2
