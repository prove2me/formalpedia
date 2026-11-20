-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageLaplaceIntegrableOfContinuousPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:33:11.033026+00:00
-- url     : https://prove2.me/submissions/6e411972-3537-48f2-ac0c-469a2f566747

import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceMeasurableFromTimePublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s q : ℝ) (hq : 0 ≤ q) :
    Integrable (passageLaplace (firstUpperPassage X s) q) P := by
  have hτ : Measurable (firstUpperPassage X s) :=
    firstUpperPassageMeasurableOfContinuousPublic
      X hMeas hContinuous s
  have hF : Measurable (passageLaplace (firstUpperPassage X s) q) :=
    passageLaplaceMeasurableFromTimePublic
      (firstUpperPassage X s) q hτ
  exact Integrable.of_bound hF.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω =>
      passageLaplaceNormBoundNonnegativeDiscountPublic
        (firstUpperPassage X s) q hq ω)
