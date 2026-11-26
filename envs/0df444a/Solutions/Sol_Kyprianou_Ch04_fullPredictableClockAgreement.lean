-- Prove2me | solution 1 for Kyprianou.Ch04.fullPredictableClockAgreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:39:55.185701+00:00
-- url     : https://prove2.me/submissions/a9872043-f49a-4c1f-b220-9e177fdfe8e7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_markedFullPredictableMeasureExists
import Theorems.Thm_Kyprianou_Ch04_markedFullClockAEMeasurable
import Theorems.Thm_Kyprianou_Ch04_markedExpectedIntegralExhaustion
import Theorems.Thm_Kyprianou_Ch04_predictableCompensationFiniteBandFromRectangleCounts
import Theorems.Thm_Kyprianou_Ch04_predictableRectangleCountFactorisation
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full predictable expected clock measure represents both raw and intensity integrals. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N) (t : NNReal) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
    ∃ mu : @Measure ((NNReal × Omega) × ℝ) m,
      ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable[m] f →
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P) := by
  let B := spanningSets nu
  have hB := measurableSet_spanningSets nu
  have hbfin := measure_spanningSets_lt_top nu
  have hmono := monotone_spanningSets nu
  have hcover := iUnion_spanningSets nu
  have hfin (n : ℕ) : referenceIntensity nu (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n) ≠ ⊤ :=
    closedTimeBandIntensityFinite nu t (B n) (hbfin n)
  have hraw (n : ℕ) : ∀ᵐ w ∂P, N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n) ≠ ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod (hB n)) (hfin n)] with w hw
    obtain ⟨k,hk⟩ := hw
    change N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets nu n) ≠ ⊤
    rw [hk]
    exact ENNReal.natCast_ne_top k
  obtain ⟨mu,hmu⟩ := markedFullPredictableMeasureExists P nu F t
  refine ⟨mu, fun f hf => ?_⟩
  have hR := markedFullClockAEMeasurable P F N.N
    (fun _ h => N.measurable_eval h) t B hB hmono hcover hraw f hf
  have hS := markedFullClockAEMeasurable P F (fun _ => referenceIntensity nu)
    (fun _ _ => measurable_const) t B hB hmono hcover
    (fun n => Eventually.of_forall fun _ => hfin n) f hf
  have hRe := markedExpectedIntegralExhaustion P F N.N
    (fun _ h => N.measurable_eval h) t B hB hmono hcover hraw f hf
  have hSe := markedExpectedIntegralExhaustion P F (fun _ => referenceIntensity nu)
    (fun _ _ => measurable_const) t B hB hmono hcover
    (fun n => Eventually.of_forall fun _ => hfin n) f hf
  have hband (n : ℕ) :
      (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) =
      (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P) := by
    exact predictableCompensationFiniteBandFromRectangleCounts P nu F N
      (predictableRectangleCountFactorisation P nu F N hFuture) t (B n) (hB n) (hbfin n) f hf
  have he := hRe.trans ((congrArg iSup (funext hband)).trans hSe.symm)
  exact ⟨hR,hS,(hmu f hf).trans he.symm,hmu f hf⟩
