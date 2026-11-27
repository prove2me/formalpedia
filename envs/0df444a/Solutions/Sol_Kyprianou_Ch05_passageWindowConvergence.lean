-- Prove2me | solution 1 for Kyprianou.Ch05.passageWindowConvergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:45:15.687211+00:00
-- url     : https://prove2.me/submissions/226c400f-c1f2-4e37-a1d5-1f5ff0dc80d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_passageWindowConvergenceLipschitz
import Theorems.Thm_Kyprianou_Ch05_passageWindowConvergenceApproximation
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
    ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop,
      |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  exact Kyprianou.Ch05.passageWindowConvergenceApproximation
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice
    (fun f hf hf0 hC => Kyprianou.Ch05.passageWindowConvergenceLipschitz
      P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
      hFiniteMean hPositiveMean hNonLattice f hf hf0 hC)
