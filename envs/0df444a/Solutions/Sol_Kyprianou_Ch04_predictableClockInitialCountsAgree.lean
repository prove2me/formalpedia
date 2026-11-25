-- Prove2me | solution 1 for Kyprianou.Ch04.predictableClockInitialCountsAgree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:17.669673+00:00
-- url     : https://prove2.me/submissions/7e3c56b5-5f45-41a5-a545-c5a8245b0d4d

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
    (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hA : MeasurableSet[F 0] A) :
    (∫⁻ w, N.N w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' ({0} : Set NNReal)) ×ˢ
      (B ∩ C)) * A.indicator (fun _ => (1 : ENNReal)) w ∂P) =
    (∫⁻ w, referenceIntensity levyMeasure
      ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' ({0} : Set NNReal)) ×ˢ (B ∩ C)) *
      A.indicator (fun _ => (1 : ENNReal)) w ∂P) := by
  classical
  have he : Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' ({0} : Set NNReal) =
      ({0} : Set Real) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_singleton_iff,
      Real.toNNReal_eq_zero]
    constructor
    · rintro ⟨⟨hs0, _⟩, hsle⟩
      exact le_antisymm hsle hs0
    · rintro rfl
      exact ⟨⟨le_rfl, t.2⟩, le_rfl⟩
  rw [he]
  have hzero : referenceIntensity levyMeasure (({0} : Set Real) ×ˢ (B ∩ C)) = 0 := by
    rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply (measurableSet_singleton 0)]
    simp
  rw [hzero]
  simp only [zero_mul, lintegral_zero]
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∫⁻ w, N.N w (({0} : Set Real) ×ˢ (B ∩ C)) ∂P := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ A <;> simp [Set.indicator, hw]
    _ = 0 := (Kyprianou.Ch02.prmCountFirstMomentENNRealV1 P levyMeasure N _
      ((measurableSet_singleton 0).prod (hB.inter hC))).trans hzero
