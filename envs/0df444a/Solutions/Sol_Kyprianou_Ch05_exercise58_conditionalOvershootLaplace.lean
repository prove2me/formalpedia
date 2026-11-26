-- Prove2me | solution 1 for Kyprianou.Ch05.exercise58_conditionalOvershootLaplace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:05:34.809011+00:00
-- url     : https://prove2.me/submissions/f178700c-bfaf-4e1d-997f-b5e813bfbbf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise58_crossingProbability
import Theorems.Thm_Kyprianou_Ch05_killedOvershootUnconditionalTransformV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
open Kyprianou.Ch05

/-- Exercise 5.8, full five parts including the alpha=0 escape case. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d alpha : Real) (Pi : Measure Real)
    (Phi : Real → Real) (U : Real → Measure Real)
    (hEta : 0 < eta)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
         Real.exp (-(t : Real) * (Phi theta-eta)))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hClassL : IsTailRatioClassL (U 0) alpha)
    (hExtMoment : IntegrableOn
      (fun z : Real => Real.exp (alpha*z)-1) (Set.Ioi 0) Pi)
    (hExtendedPhi : Phi (-alpha) = eta-d*alpha +
      ∫ z in Set.Ioi (0 : Real),
         (1-Real.exp (alpha*z)) ∂Pi)
 :
  (∀ beta x : Real, 0 ≤ beta → 0 ≤ x →
     conditionalOvershootTransform P Y death beta x =
       Phi beta / (eta * (U 0 (Set.Ioi x)).toReal) *
         (∫ z in Set.Ioi x, Real.exp (-beta*(z-x)) ∂(U 0)))
 := by
  intro beta x hbeta hx
  unfold conditionalOvershootTransform
  dsimp only
  rw [exercise58_crossingProbability P Y death eta d alpha Pi Phi U hEta
    hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi x hx,
    killedOvershootUnconditionalTransformV1 P Y death eta d Pi Phi U hEta
      hKilled hTriplet hLaplaceLaw hPotential beta x hbeta hx]
  ring
