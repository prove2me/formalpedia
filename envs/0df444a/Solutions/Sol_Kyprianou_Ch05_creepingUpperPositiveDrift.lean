-- Prove2me | solution 1 for Kyprianou.Ch05.creepingUpperPositiveDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T00:56:02.939933+00:00
-- url     : https://prove2.me/submissions/099f1542-66b9-4079-9f34-17c5920efcc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingPotentialRatioLimit
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
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, creepingProbability P Y death x ≤ d / (∫ omega, Y 1 omega ∂P) + ε := by
  intro ε hε
  have hμ : 0 < (∫ omega, Y 1 omega ∂P) := hPositiveMean
  have hr := Kyprianou.Ch05.creepingPotentialRatioLimit P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential hFiniteMean hPositiveMean hNonLattice hPotLim hd
  have hp := hPotLim 1 one_pos
  have hpos : ∀ᶠ x : Real in atTop, (0:Real) < ((U 0) (Set.Ioc x (x + 1))).toReal :=
    hp.eventually (eventually_gt_nhds (one_div_pos.mpr hμ))
  have hmul := hr.mul hp
  have heq : ∀ᶠ x : Real in atTop,
      (fun x : Real => creepingProbability P Y death x / ((U 0) (Set.Ioc x (x + 1))).toReal * ((U 0) (Set.Ioc x (x + 1))).toReal) x
        = creepingProbability P Y death x :=
    hpos.mono fun x hx => div_mul_cancel₀ _ (ne_of_gt hx)
  have hlim : Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds (d / (∫ omega, Y 1 omega ∂P))) := by
    have h2 := hmul.congr' heq
    rwa [show d * (1 / (∫ omega, Y 1 omega ∂P)) = d / (∫ omega, Y 1 omega ∂P) by ring] at h2

  have h := Metric.tendsto_nhds.mp hlim ε hε
  filter_upwards [h] with x hx
  have hx2 : |creepingProbability P Y death x - d / (∫ omega, Y 1 omega ∂P)| < ε := by
    rwa [Real.dist_eq] at hx
  have h12 := abs_sub_lt_iff.mp hx2
  linarith [h12.1, h12.2]
