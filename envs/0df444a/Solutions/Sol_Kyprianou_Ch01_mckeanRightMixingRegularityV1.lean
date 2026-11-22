-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightMixingRegularityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:57:06.870034+00:00
-- url     : https://prove2.me/submissions/2f1a71d2-1aba-48dc-9ff9-13df72800408

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (s : ℝ≥0)
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ (F s) inferInstance Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P) :
    Integrable (fun ω => f (Y ω + Z ω)) P ∧
    Integrable (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) P ∧
    AEStronglyMeasurable[F s]
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) P := by
  have hY : Measurable Y := hYm.mono (F.le s) le_rfl
  have hCurMeas : Measurable (fun ω => f (Y ω + Z ω)) :=
    hf.comp (hY.add hZm)
  have hCurInt : Integrable (fun ω => f (Y ω + Z ω)) P :=
    Integrable.of_bound hCurMeas.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => hBound _)
  have hPair : Measurable (fun p : ℝ × Ω => f (p.1 + Z p.2)) :=
    hf.comp (measurable_fst.add (hZm.comp measurable_snd))
  have hParam :
      Measurable (fun y : ℝ => ∫ ξ, f (y + Z ξ) ∂P) :=
    hPair.stronglyMeasurable.integral_prod_right' |>.measurable
  have hGStrong :
      StronglyMeasurable[F s]
        (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) :=
    (hParam.comp hYm).stronglyMeasurable
  have hGMeas :
      Measurable (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) :=
    hGStrong.measurable.mono (F.le s) le_rfl
  have hGBound (ω : Ω) :
      ‖∫ ξ, f (Y ω + Z ξ) ∂P‖ ≤ K := by
    simpa using (norm_integral_le_of_norm_le_const
      (μ := P) (Filter.Eventually.of_forall
        (fun ξ => hBound (Y ω + Z ξ))))
  have hGInt : Integrable (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) P :=
    Integrable.of_bound hGMeas.aestronglyMeasurable K
      (Filter.Eventually.of_forall hGBound)
  exact ⟨hCurInt, hGInt, hGStrong.aestronglyMeasurable⟩
