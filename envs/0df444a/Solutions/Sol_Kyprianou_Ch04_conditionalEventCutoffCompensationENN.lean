-- Prove2me | solution 1 for Kyprianou.Ch04.conditionalEventCutoffCompensationENN
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:08:22.616792+00:00
-- url     : https://prove2.me/submissions/b1a04d85-a380-408f-b344-caceac362942

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_commonNullEventCutoffAdmissible
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

/-- Conditional event cutoff: extended Poisson compensation. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ w ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => phi s x w)
        (nhdsWithin (r : Real) (Set.Iio (r : Real))) (nhds (phi (r : Real) x w)))
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (if (u : Real) < z.1 ∧ w ∈ A then phi z.1 z.2 w else 0)
      ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (if (u : Real) < s ∧ w ∈ A then phi s x w else 0)
        ∂levyMeasure) ∂volume ∂P) := by
  obtain ⟨hK, hC⟩ := commonNullEventCutoffAdmissible P F phi hPhi hCommon u A hA
  exact nonnegativePredictableJumpCompensationCommonNullV2 P levyMeasure F N
    hFuture _ hK hC t
