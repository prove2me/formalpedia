-- Prove2me | solution 1 for Kyprianou.Ch05.exercise55ExponentialPassageAllParts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:45:05.623625+00:00
-- url     : https://prove2.me/submissions/60558367-a5cd-4eb7-9fda-479fb5ff9c8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_exercise55_discountedPassageMoment
import Theorems.Thm_Kyprianou_Ch05_exercise55_overshootDoubleLaplace
import Theorems.Thm_Kyprianou_Ch05_exercise55_creepingDensityBoundary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exercise 5.5, all four subparts, including equation (5.20). -/
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
    (hLeft : IsLeftLimitVersion P Y Yleft)
 :
    -- (i) Finite-positive prefactor: a finite ordinary integral
  -- gives the strong-Markov identity. The zero-prefactor case is
  -- stated separately, avoiding the undefined 0 times infinity.
  ((∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
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
            exponentialFirstPassageMoment P Y death alpha beta x = 0)))) ∧
   -- (ii) The q>beta transform is valid with positive denominator.
   -- The identically zero subordinator has zero passage transform.
   (∀ alpha beta q : Real, 0 ≤ alpha → 0 ≤ beta → beta < q →
      ((0 < alpha + Phi q →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) =
          (1 - (alpha + Phi beta) / (alpha + Phi q)) / (q-beta)) ∧
       (alpha + Phi q = 0 →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) = 0))) ∧
-- (iii) Exact creeping identity, including d=0 and the
   -- continuous strictly positive density when d>0.
   ((d = 0 →
      ∀ alpha x : Real, 0 ≤ alpha → 0 < x →
        exponentialCreepingMoment P Y death alpha x = 0) ∧
    (0 < d →
      ∀ alpha : Real, 0 ≤ alpha →
        ∃ ualpha : Real → Real,
          ContinuousOn ualpha (Set.Ioi (0 : Real)) ∧
          (∀ x : Real, 0 < x → 0 < ualpha x) ∧
          ((U alpha).restrict (Set.Ioi (0 : Real)) =
            ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal (ualpha x))) ∧
          (∀ x : Real, 0 < x →
            exponentialCreepingMoment P Y death alpha x =
              d * ualpha x) ∧
          -- (iv) For the same density version, u^(alpha)(0+)=1/d.
          Tendsto ualpha
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 / d)))))
 := by
  exact ⟨
    Kyprianou.Ch05.exercise55_discountedPassageMoment P Y Yleft death d Pi Phi U hKilled hTriplet hLaplaceLaw hPotential hLeft,
    Kyprianou.Ch05.exercise55_overshootDoubleLaplace P Y Yleft death d Pi Phi U hKilled hTriplet hLaplaceLaw hPotential hLeft,
    Kyprianou.Ch05.exercise55_creepingDensityBoundary P Y Yleft death d Pi Phi U hKilled hTriplet hLaplaceLaw hPotential hLeft
  ⟩

