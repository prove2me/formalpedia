-- Prove2me | solution 1 for Kyprianou.Ch04.predictableRectangleCountFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:47:31.899482+00:00
-- url     : https://prove2.me/submissions/78e18ea8-e7b2-43e4-a126-ee57021e715a

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
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N) :
    ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A := by
  intro u v B A huv hB hA
  let f : Omega → ENNReal := fun omega =>
    N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B)
  have hS : MeasurableSet (Set.Ioc (u : Real) (v : Real) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hf : Measurable f := N.measurable_eval hS
  have hf' : Measurable[MeasurableSpace.comap f inferInstance] f :=
    comap_measurable f
  have hg : Measurable[F u] (A.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hA
  have hi := hFuture u v B huv hB
  change (∫⁻ omega, f omega * A.indicator (fun _ => (1 : ENNReal)) omega ∂P) = _
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    hf.comap_le (F.le u) hi hf' hg]
  have hIndicator :
      (∫⁻ omega, A.indicator (fun _ => (1 : ENNReal)) omega ∂P) = P A := by
    exact lintegral_indicator_one (F.le u _ hA)
  rw [Kyprianou.Ch02.prmCountFirstMomentENNRealV1 P levyMeasure N _ hS, hIndicator]
