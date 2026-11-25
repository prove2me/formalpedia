-- Prove2me | solution 1 for Kyprianou.Ch04.predictableClockGeneratorCountsAgree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:34.95413+00:00
-- url     : https://prove2.me/submissions/e8f4154e-6255-4b3f-b537-24219a3dd74f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch02_prmCountFirstMomentENNRealV1
import Theorems.Thm_Kyprianou_Ch04_predictableClockInitialCountsAgree
import Theorems.Thm_Kyprianou_Ch04_predictableClockFutureCountsAgree
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
    (D : Set NNReal) (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hGen : (D = {0} ∧ MeasurableSet[F 0] A) ∨
      (∃ i : NNReal, D = Set.Ioi i ∧ MeasurableSet[F i] A)) :
    (∫⁻ w, N.N w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' D) ×ˢ
      (B ∩ C)) * A.indicator (fun _ => (1 : ENNReal)) w ∂P) =
    (∫⁻ w, referenceIntensity levyMeasure
      ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' D) ×ˢ (B ∩ C)) *
      A.indicator (fun _ => (1 : ENNReal)) w ∂P) := by
  rcases hGen with ⟨rfl, hA⟩ | ⟨i, rfl, hA⟩
  · exact predictableClockInitialCountsAgree P levyMeasure F N hRect t B hB A C hC hA
  · exact predictableClockFutureCountsAgree P levyMeasure F N hRect t B hB i A C hC hA
