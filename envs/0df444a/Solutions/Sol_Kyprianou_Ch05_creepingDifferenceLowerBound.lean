-- Prove2me | solution 1 for Kyprianou.Ch05.creepingDifferenceLowerBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:29:52.417808+00:00
-- url     : https://prove2.me/submissions/08043d64-fa7c-4c1e-bb35-ab4a8328cbbc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingLowerRelativeBound
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
    (hd : 0 < d) :
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop,
    -ε ≤ creepingProbability P Y death x - d * ((U 0) (Set.Ioc x (x + 1))).toReal := by
  intro ε hε
  have hμ : 0 < (∫ omega, Y 1 omega ∂P) := hPositiveMean
  have hδ : 0 < ε * (∫ omega, Y 1 omega ∂P) / 2 := by
    have h := mul_pos hε hμ
    linarith
  have h1 := Kyprianou.Ch05.creepingLowerRelativeBound
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice hPotLim hd (ε * (∫ omega, Y 1 omega ∂P) / 2) hδ
  have hlim : Tendsto (fun x : Real => (ε * (∫ omega, Y 1 omega ∂P) / 2) * ((U 0) (Set.Ioc x (x + 1))).toReal)
      atTop (nhds (ε / 2)) := by
    have hp := (hPotLim 1 one_pos).const_mul (ε * (∫ omega, Y 1 omega ∂P) / 2)
    rwa [show (ε * (∫ omega, Y 1 omega ∂P) / 2) * (1 / (∫ omega, Y 1 omega ∂P)) = ε / 2 by
      field_simp] at hp
  have h2 := Metric.tendsto_nhds.mp hlim (ε / 2) (half_pos hε)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [sub_mul] at hx1
  rw [Real.dist_eq] at hx2
  have hlt := (abs_lt.mp hx2).2
  linarith
