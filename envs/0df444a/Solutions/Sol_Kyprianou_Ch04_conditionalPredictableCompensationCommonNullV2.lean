-- Prove2me | solution 1 for Kyprianou.Ch04.conditionalPredictableCompensationCommonNullV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:08:43.171013+00:00
-- url     : https://prove2.me/submissions/7edc7df6-d871-44cc-99a7-9607541231bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_commonNullEventCutoffAdmissible
import Theorems.Thm_Kyprianou_Ch04_eventCutoffRawIntegral
import Theorems.Thm_Kyprianou_Ch04_eventCutoffIntensityIntegral
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
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
    forall u t : NNReal, u <= t ->
      forall A : Set Omega, MeasurableSet[F u] A ->
      (∫⁻ omega in A,
        (∫⁻ z in Set.prod (Set.Ioc (u : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
      (∫⁻ omega in A,
        (∫⁻ s in Set.Ioc (u : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) := by

  intro u t hut A hA
  classical
  let psi : Real → Real → Omega → Real :=
    fun s x omega => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0
  obtain ⟨hadm, hleft⟩ := commonNullEventCutoffAdmissible P F phi hPhi hCommon u A hA
  have hAm : MeasurableSet A := F.le u A hA
  have hN := eventCutoffRawIntegral P levyMeasure N phi u t A hAm
  have hν := eventCutoffIntensityIntegral P levyMeasure phi u t A hAm
  exact hN.symm.trans ((nonnegativePredictableJumpCompensationCommonNullV2
    P levyMeasure F N hFuture psi hadm hleft t).trans hν)
