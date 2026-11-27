-- Prove2me | solution 1 for Kyprianou.Ch05.creepingProbabilityTendstoZeroOfZeroDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:19:47.142014+00:00
-- url     : https://prove2.me/submissions/96d8d0b7-49a3-46c9-811a-0668ce4e7232
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingZeroDriftEventualBound
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
    (hPotLim : ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P))))
    (hd : d = 0) :
  Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := Kyprianou.Ch05.creepingZeroDriftEventualBound
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice hPotLim hd (ε / 2) (half_pos hε)
  filter_upwards [h] with x hx
  have hnn : 0 ≤ creepingProbability P Y death x := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith
