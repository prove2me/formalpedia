-- Prove2me | solution 1 for Kyprianou.Ch05.exercise58KilledTailRatioAllParts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:45:24.292523+00:00
-- url     : https://prove2.me/submissions/3dac2530-e73c-49d2-83bd-73dac3ffab25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
import Theorems.Thm_Kyprianou_Ch05_exercise58_crossingProbability
import Theorems.Thm_Kyprianou_Ch05_exercise58_conditionalOvershootLaplace
import Theorems.Thm_Kyprianou_Ch05_exercise58_tailRatioLimit
import Theorems.Thm_Kyprianou_Ch05_exercise58_positiveAlphaLimitLaw
import Theorems.Thm_Kyprianou_Ch05_exercise58_zeroAlphaEscape
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
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
  -- (i) Crossing probability is eta times the potential tail.
  ((∀ x : Real, 0 ≤ x →
    (P {omega : Omega | PassageFinite Y death x omega}).toReal =
       eta*(U 0 (Set.Ioi x)).toReal) ∧
   -- (ii) Finite-level conditional overshoot Laplace transform.
   (∀ beta x : Real, 0 ≤ beta → 0 ≤ x →
     conditionalOvershootTransform P Y death beta x =
       Phi beta / (eta * (U 0 (Set.Ioi x)).toReal) *
         (∫ z in Set.Ioi x, Real.exp (-beta*(z-x)) ∂(U 0))) ∧
   -- (iii) The class-L limit. beta=alpha=0 is an exact removable
   -- boundary case, whose value must be one.
   (∀ beta : Real, 0 ≤ beta →
     Tendsto
       (fun x : Real => conditionalOvershootTransform P Y death beta x)
       atTop
       (nhds (if beta = 0 then 1
          else (Phi beta / eta) * (alpha / (alpha+beta))))) ∧
   -- (iv) For alpha>0 the limit is a genuine probability measure:
   -- its atom at zero and its positive-overshoot Laplace transform
   -- are both required, with no missing creeping contribution.
   (0 < alpha →
     ∃ G : Measure Real, IsProbabilityMeasure G ∧
       G (Set.Iio (0 : Real)) = 0 ∧
       G {0} = ENNReal.ofReal (d*alpha/eta) ∧
       (∀ u : Real, 0 ≤ u →
         (G (Set.Ioi u)).toReal =
           limitingKilledOvershootTail eta alpha Phi Pi u) ∧
       (∀ beta : Real, 0 ≤ beta →
         ∫ z in Set.Ioi (0 : Real),
           Real.exp (-beta*z) ∂G =
           (alpha*Phi beta / (eta*(alpha+beta))) -
              d*alpha/eta) ∧
       -- (v) Weak tail limit and exact creeping atom.
       (∀ u : Real, 0 ≤ u →
         Tendsto
           (fun x : Real =>
             (P {omega : Omega |
               PassageFinite Y death x omega ∧
               u < passageOvershoot Y death x omega}).toReal /
                 (P {omega : Omega |
                   PassageFinite Y death x omega}).toReal)
           atTop (nhds ((G (Set.Ioi u)).toReal))) ∧
       Tendsto
         (fun x : Real =>
           (P {omega : Omega |
             PassageFinite Y death x omega ∧
             passageOvershoot Y death x omega = 0}).toReal /
             (P {omega : Omega |
                 PassageFinite Y death x omega}).toReal)
         atTop (nhds (d*alpha/eta))) ∧
   -- At alpha=0, finite-level conditional laws escape to infinity.
   -- The printed generic probability limit needs a point at infinity.
   (alpha = 0 →
     (∀ u : Real, 0 ≤ u →
       Tendsto
         (fun x : Real =>
           (P {omega : Omega |
             PassageFinite Y death x omega ∧
             u < passageOvershoot Y death x omega}).toReal /
             (P {omega : Omega |
               PassageFinite Y death x omega}).toReal)
         atTop (nhds 1)) ∧
      Tendsto
        (fun x : Real =>
          (P {omega : Omega |
            PassageFinite Y death x omega ∧
            passageOvershoot Y death x omega = 0}).toReal /
             (P {omega : Omega |
                PassageFinite Y death x omega}).toReal)
        atTop (nhds 0)))
 := by
  exact ⟨
    Kyprianou.Ch05.exercise58_crossingProbability P Y death eta d alpha Pi Phi U hEta hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi,
    Kyprianou.Ch05.exercise58_conditionalOvershootLaplace P Y death eta d alpha Pi Phi U hEta hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi,
    Kyprianou.Ch05.exercise58_tailRatioLimit P Y death eta d alpha Pi Phi U hEta hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi,
    Kyprianou.Ch05.exercise58_positiveAlphaLimitLaw P Y death eta d alpha Pi Phi U hEta hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi,
    Kyprianou.Ch05.exercise58_zeroAlphaEscape P Y death eta d alpha Pi Phi U hEta hKilled hTriplet hLaplaceLaw hPotential hClassL hExtMoment hExtendedPhi
  ⟩

