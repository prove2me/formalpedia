-- Prove2me | solution 1 for Kyprianou.Ch05.jointAssemblyLowerBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:17:35.345783+00:00
-- url     : https://prove2.me/submissions/af4a3452-5231-4537-b608-158401ba6134
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_jointAssemblyLowerWindowBound
import Theorems.Thm_Kyprianou_Ch05_jointAssemblyLowerTailBound
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
    (hNonLattice : NonLatticeMeasure (U 0))
    (hVan : ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
     Tendsto (fun x : Real => passageTestExpectation P Y Yleft death x f) atTop
       (nhds ((1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume))))
    (hCreep : Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds (d / (∫ omega, Y 1 omega ∂P)))) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, d / (∫ omega, Y 1 omega ∂P) * f (0, 0) + (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - ε ≤ passageTestExpectation P Y Yleft death x f := by
  intro f hf ε hε
  have hw := Kyprianou.Ch05.jointAssemblyLowerWindowBound P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential hFiniteMean hPositiveMean hNonLattice hVan hCreep f hf (ε / 2) (half_pos hε)
  have ht := Kyprianou.Ch05.jointAssemblyLowerTailBound P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential hFiniteMean hPositiveMean hNonLattice hVan hCreep f hf (ε / 2) (half_pos hε)
  filter_upwards [hw, ht] with x hxw hxt
  linarith
