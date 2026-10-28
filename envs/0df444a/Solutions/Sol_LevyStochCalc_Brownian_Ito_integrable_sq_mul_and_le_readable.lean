-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:24.813337+00:00
-- url     : https://prove2.me/submissions/6bb71d25-1ebb-4805-a725-84c5d595cf6d

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
omit [IsProbabilityMeasure P] in
/-- The square of a product of two functions with integrable fourth powers is integrable, and its
integral is at most half the sum of the two fourth moments. -/
theorem solution {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA4 : Integrable (fun ω => A ω ^ 4) P) (hB4 : Integrable (fun ω => B ω ^ 4) P) :
    Integrable (fun ω => (A ω * B ω) ^ 2) P
      ∧ ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ (∫ ω, A ω ^ 4 ∂P + ∫ ω, B ω ^ 4 ∂P) / 2 := by
  have hdom : Integrable (fun ω => (A ω ^ 4 + B ω ^ 4) / 2) P := (hA4.add hB4).div_const 2
  have hpt : ∀ ω, (A ω * B ω) ^ 2 ≤ (A ω ^ 4 + B ω ^ 4) / 2 := fun ω => by
    nlinarith [sq_nonneg (A ω ^ 2 - B ω ^ 2), sq_nonneg (A ω * B ω)]
  have hint : Integrable (fun ω => (A ω * B ω) ^ 2) P := by
    refine Integrable.mono' hdom ((hAm.mul hBm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hle : ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ ∫ ω, (A ω ^ 4 + B ω ^ 4) / 2 ∂P :=
    MeasureTheory.integral_mono hint hdom hpt
  rwa [MeasureTheory.integral_div, MeasureTheory.integral_add hA4 hB4] at hle
