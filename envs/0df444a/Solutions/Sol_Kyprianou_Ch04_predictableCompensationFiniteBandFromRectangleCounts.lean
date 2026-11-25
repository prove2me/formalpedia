-- Prove2me | solution 1 for Kyprianou.Ch04.predictableCompensationFiniteBandFromRectangleCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:03.665267+00:00
-- url     : https://prove2.me/submissions/44c18f08-46c0-4201-8923-41a69396260b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
import Theorems.Thm_Kyprianou_Ch04_markedClockRectangleEval
import Theorems.Thm_Kyprianou_Ch04_predictableClockGeneratorCountsAgree
import Theorems.Thm_Kyprianou_Ch02_prmCountFirstMomentENNRealV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hRect : ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A)
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hBfin : levyMeasure B < ⊤)
    (f : ((NNReal × Omega) × Real) → ENNReal) (hf : Measurable[F.predictable.prod inferInstance] f) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(referenceIntensity levyMeasure) ∂P) := by
  have hU : MeasurableSet (Set.Icc (0 : Real) (t : Real) ×ˢ B) :=
    measurableSet_Icc.prod hB
  have hfin := closedTimeBandIntensityFinite levyMeasure t B hBfin
  have hR : ∀ᵐ w ∂P, N.N w (Set.Icc (0 : Real) (t : Real) ×ˢ B) ≠ ⊤ := by
    filter_upwards [N.integer_valued hU hfin] with w hw
    obtain ⟨k, hk⟩ := hw
    simp [hk]
  obtain ⟨M, hM⟩ := finiteMarkedClockMeasure P F N.N
    (fun S hS => N.measurable_eval hS) t B hB hR
  obtain ⟨Q, hQ⟩ := finiteMarkedClockMeasure P F (fun _ => referenceIntensity levyMeasure)
    (fun _ _ => measurable_const) t B hB (Filter.Eventually.of_forall (fun _ => hfin))
  have hMass : M Set.univ =
      ∫⁻ w, N.N w (Set.Icc (0 : Real) (t : Real) ×ˢ B) ∂P := by
    simpa only [lintegral_one, Measure.restrict_apply_univ] using
      (hM (fun _ => 1) measurable_const).2
  letI : IsFiniteMeasure M := ⟨by
    rw [hMass, Kyprianou.Ch02.prmCountFirstMomentENNRealV1 P levyMeasure N _ hU]
    exact lt_top_iff_ne_top.mpr hfin⟩
  have hAgree (D : Set NNReal) (A : Set Omega) (C : Set Real)
      (hD : MeasurableSet D) (hC : MeasurableSet C)
      (hDC : MeasurableSet[F.predictable.prod inferInstance] ((D ×ˢ A) ×ˢ C))
      (hGen : (D = {0} ∧ MeasurableSet[F 0] A) ∨
        (∃ i : NNReal, D = Set.Ioi i ∧ MeasurableSet[F i] A)) :
      M ((D ×ˢ A) ×ˢ C) = Q ((D ×ˢ A) ×ˢ C) := by
    rw [markedClockRectangleEval P F N.N t B hB M (fun g hg => (hM g hg).2)
        D hD A C hC hDC,
      markedClockRectangleEval P F (fun _ => referenceIntensity levyMeasure)
        t B hB Q (fun g hg => (hQ g hg).2) D hD A C hC hDC]
    exact predictableClockGeneratorCountsAgree P levyMeasure F N hRect t B hB D A C hC hGen
  have he : M = Q :=
    AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique F M Q
      (fun A C hA hC =>
        hAgree {0} A C (measurableSet_singleton 0) hC
          ((measurableSet_predictable_singleton_bot_prod hA).prod hC) (Or.inl ⟨rfl, hA⟩))
      (fun i A C hA hC =>
        hAgree (Set.Ioi i) A C measurableSet_Ioi hC
          ((measurableSet_predictable_Ioi_prod hA).prod hC) (Or.inr ⟨i, rfl, hA⟩))
  rw [← (hM f hf).2, ← (hQ f hf).2, he]
