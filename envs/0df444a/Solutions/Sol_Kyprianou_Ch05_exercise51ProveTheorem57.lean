-- Prove2me | solution 1 for Kyprianou.Ch05.exercise51ProveTheorem57
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:38:27.135729+00:00
-- url     : https://prove2.me/submissions/0bdff687-40ee-4502-a85d-8d204af92e16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch05_finiteMeanPassageJointWeakLimit
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05

/-- Theorem 5.7, p.121: entire finite-mean weak joint law,
including the creeping mass d/mu at (0,0), and its separate limit. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  let mu : Real := ∫ omega, Y 1 omega ∂P
  ((∀ f : Real × Real → Real, IsBoundedContinuousTest f →
     Tendsto
       (fun x : Real => passageTestExpectation P Y Yleft death x f)
       atTop
       (nhds
         (d / mu * f (0,0) +
           (1 / mu) *
             (∫ y in Set.Ici (0 : Real),
                ∫ z in Set.Ioi y, f (z-y,y) ∂Pi ∂volume)))) ∧
   (Tendsto (fun x : Real => creepingProbability P Y death x)
     atTop (nhds (d / mu))))
 := by
  exact Kyprianou.Ch05.finiteMeanPassageJointWeakLimit P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential hFiniteMean hPositiveMean hNonLattice

