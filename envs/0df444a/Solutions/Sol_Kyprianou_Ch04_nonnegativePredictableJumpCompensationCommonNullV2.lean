-- Prove2me | solution 1 for Kyprianou.Ch04.nonnegativePredictableJumpCompensationCommonNullV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:05:04.455113+00:00
-- url     : https://prove2.me/submissions/b17a0158-b87f-46a1-b2bf-a8b3349346f9

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_commonNullPredictableENNRepresentative
import Theorems.Thm_Kyprianou_Ch04_jointlyPredictableENNJumpCompensation
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
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega))) :
    forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) := by
  obtain ⟨psi, hPsi, hEq⟩ :=
    commonNullPredictableENNRepresentative P F phi hPhi hCommon
  intro t
  calc
    _ = (∫⁻ omega,
        (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          psi z.1 z.2 omega ∂(N.N omega)) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hEq] with omega h
      exact lintegral_congr (fun z => (h z.1 z.2).symm)
    _ = (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, psi s x omega ∂levyMeasure) ∂volume) ∂P) :=
      jointlyPredictableENNJumpCompensation P levyMeasure F N hFuture psi hPsi t
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hEq] with omega h
      exact lintegral_congr (fun s => lintegral_congr (fun x => h s x))
