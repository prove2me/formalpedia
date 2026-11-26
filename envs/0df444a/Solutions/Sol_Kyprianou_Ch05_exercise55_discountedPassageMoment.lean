-- Prove2me | solution 1 for Kyprianou.Ch05.exercise55_discountedPassageMoment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:47:00.313335+00:00
-- url     : https://prove2.me/submissions/3bbc410b-367a-4c98-9dce-ccdbb6cc4b17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Theorems.Thm_Kyprianou_Ch05_completeStrictPassageMarkovLaw
import Theorems.Thm_Kyprianou_Ch05_exercise55FutureFactorOfCompleteMarkovLaw
import Theorems.Thm_Kyprianou_Ch05_exercise55DiscountedPassageOfFutureFactor
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
/-- Separate regenerative future factor from discounted occupation calculus. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft) :
  (∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ((0 < alpha + Phi beta →
        IntegrableOn (fun z : Real => Real.exp (-beta*z))
          (Set.Ioi x) (U alpha) ∧
        exponentialFirstPassageMoment P Y death alpha beta x =
          (alpha + Phi beta) *
            ∫ z in Set.Ioi x, Real.exp (-beta*z) ∂(U alpha)) ∧
       (alpha + Phi beta = 0 →
         (beta = 0 →
            exponentialFirstPassageMoment P Y death alpha beta x =
              (P {omega : Omega | PassageFinite Y death x omega}).toReal) ∧
         (0 < beta →
            exponentialFirstPassageMoment P Y death alpha beta x = 0)))) := by
  apply exercise55DiscountedPassageOfFutureFactor P Y Yleft death d Pi Phi U
    hKilled hTriplet hLaplaceLaw hPotential hLeft
  exact exercise55FutureFactorOfCompleteMarkovLaw P Y Yleft death d Pi Phi U
    hKilled hTriplet hLaplaceLaw hPotential hLeft completeStrictPassageMarkovLaw
