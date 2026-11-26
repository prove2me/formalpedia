-- Prove2me | solution 1 for Kyprianou.Ch04.finiteBandPredictableClockAgreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:51:37.27619+00:00
-- url     : https://prove2.me/submissions/4810e069-ec8e-4e23-a944-256615161735

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_predictableRectangleCountFactorisation
import Theorems.Thm_Kyprianou_Ch04_predictableCompensationFiniteBandFromRectangleCounts
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite predictable clock measure represents both random and intensity integrals. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B) (hBfin : nu B < ⊤) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace Real)
    ∃ mu : @Measure ((NNReal × Omega) × Real) m,
      IsFiniteMeasure mu ∧
      ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[m] f →
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P) := by
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  have hfin : referenceIntensity nu U ≠ ⊤ :=
    closedTimeBandIntensityFinite nu t B hBfin
  have hraw : ∀ᵐ w ∂P, N.N w U ≠ ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB) hfin] with w hw
    obtain ⟨k, hk⟩ := hw
    simp [U, hk]
  obtain ⟨M, hM⟩ := finiteMarkedClockMeasure P F N.N
    (fun S hS => N.measurable_eval hS) t B hB hraw
  obtain ⟨mu, hmu⟩ := finiteMarkedClockMeasure P F (fun _ => referenceIntensity nu)
    (fun _ _ => measurable_const) t B hB (Eventually.of_forall fun _ => hfin)
  refine ⟨mu, ?_, ?_⟩
  · refine ⟨?_⟩
    have h := (hmu (fun _ => (1 : ENNReal)) measurable_const).2
    have he : mu Set.univ = referenceIntensity nu U := by
      simpa [lintegral_const, U, Measure.restrict_apply_univ] using h
    rw [he]
    exact lt_top_iff_ne_top.mpr hfin
  · intro f hf
    have he := predictableCompensationFiniteBandFromRectangleCounts P nu F N
      (predictableRectangleCountFactorisation P nu F N hFuture) t B hB hBfin f hf
    exact ⟨(hM f hf).1, (hmu f hf).1, (hmu f hf).2.trans he.symm, (hmu f hf).2⟩
