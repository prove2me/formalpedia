-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedLowerPassageAboveBarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:16:59.817293+00:00
-- url     : https://prove2.me/submissions/e426f55b-7148-4c3b-b546-f01bcd699b84

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_spatialTranslationForMcKean
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedLowerPassage

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x barrier : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hxb : barrier ≤ x)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstLowerPassage X x barrier) q) P ∧
    (∫ ω, passageLaplace (firstLowerPassage X x barrier) q ω ∂P) =
      Real.exp (-(x - barrier) *
        ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2)) := by
  have ha : 0 ≤ x - barrier := sub_nonneg.mpr hxb
  have hmain := Kyprianou.Ch01.brownianDiscountedLowerPassage
    P X sigma gamma q (x - barrier) hsigma hq ha hB hXmeas
  have hshift :
      firstLowerPassage X x barrier =
        firstLowerPassage X 0 (-(x - barrier)) := by
    simpa only [neg_sub] using
      (Kyprianou.Ch01.firstLowerPassage_spatialTranslationForMcKean
        X x barrier)
  rw [hshift]
  exact hmain
