-- Prove2me | solution 1 for Kyprianou.Ch04.predictableClockFutureCountsAgree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:25.457726+00:00
-- url     : https://prove2.me/submissions/5348420b-45dc-4b82-b4dd-89f7b5a7c278

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch02_prmCountFirstMomentENNRealV1
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
    (i : NNReal) (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hA : MeasurableSet[F i] A) :
    (∫⁻ w, N.N w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' Set.Ioi i) ×ˢ
      (B ∩ C)) * A.indicator (fun _ => (1 : ENNReal)) w ∂P) =
    (∫⁻ w, referenceIntensity levyMeasure
      ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' Set.Ioi i) ×ˢ (B ∩ C)) *
      A.indicator (fun _ => (1 : ENNReal)) w ∂P) := by
  classical
  have he : Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' Set.Ioi i =
      Set.Ioc (i : Real) (t : Real) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hs0, hst⟩, his⟩
      have hc : (i : Real) < (s.toNNReal : Real) := by exact_mod_cast his
      rw [Real.coe_toNNReal _ hs0] at hc
      exact ⟨hc, hst⟩
    · rintro ⟨his, hst⟩
      have hs0 : 0 ≤ s := i.2.trans his.le
      refine ⟨⟨hs0, hst⟩, ?_⟩
      have hc : (i : Real) < (s.toNNReal : Real) := by rwa [Real.coe_toNNReal _ hs0]
      exact_mod_cast hc
  rw [he]
  by_cases hit : i ≤ t
  · rw [hRect i t (B ∩ C) A hit (hB.inter hC) hA]
    have hg : Measurable (A.indicator (fun _ => (1 : ENNReal))) :=
      measurable_const.indicator (F.le i _ hA)
    have hI : (∫⁻ w, A.indicator (fun _ => (1 : ENNReal)) w ∂P) = P A :=
      lintegral_indicator_one (F.le i _ hA)
    rw [lintegral_const_mul _ hg, hI]
  · have hreal : ¬ (i : Real) ≤ (t : Real) := by exact_mod_cast hit
    have hempty : Set.Ioc (i : Real) (t : Real) = ∅ := by
      ext s
      simp only [Set.mem_Ioc, Set.mem_empty_iff_false]
      exact iff_false_intro (fun hs => hreal (hs.1.le.trans hs.2))
    simp [hempty]
