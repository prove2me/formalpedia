-- Prove2me | solution 1 for Kyprianou.Ch05.creepingLimitFromPotentialLimits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:19:13.11297+00:00
-- url     : https://prove2.me/submissions/76ef1cbb-8932-460f-a84c-cc5a5c69f33d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingProbabilityUpperBoundEventually
import Theorems.Thm_Kyprianou_Ch05_creepingProbabilityLowerBoundEventually
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

/-- Bridge step for Theorem 5.7 (creeping): the nonlattice potential
interval limits determine the limiting creeping probability. -/
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
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P)))) :
  Tendsto (fun x : Real => creepingProbability P Y death x)
    atTop (nhds (d / (∫ omega, Y 1 omega ∂P))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := Kyprianou.Ch05.creepingProbabilityUpperBoundEventually
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice hPotLim (ε / 2) (half_pos hε)
  have hl := Kyprianou.Ch05.creepingProbabilityLowerBoundEventually
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice hPotLim (ε / 2) (half_pos hε)
  filter_upwards [hu, hl] with x hxu hxl
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith
