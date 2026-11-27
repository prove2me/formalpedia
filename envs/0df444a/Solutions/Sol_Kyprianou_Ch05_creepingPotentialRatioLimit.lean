-- Prove2me | solution 1 for Kyprianou.Ch05.creepingPotentialRatioLimit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:03:26.322841+00:00
-- url     : https://prove2.me/submissions/e92a86c6-965b-4e2b-bc6a-e8efd53dcb7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingPotentialDifferenceLimit
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
  Tendsto (fun x : Real => creepingProbability P Y death x / ((U 0) (Set.Ioc x (x + 1))).toReal)
    atTop (nhds d) := by
  have hμ : 0 < (∫ omega, Y 1 omega ∂P) := hPositiveMean
  have hp := hPotLim 1 one_pos
  have hU0 : ∀ᶠ x : Real in atTop, ((U 0) (Set.Ioc x (x + 1))).toReal ≠ 0 :=
    (hp.eventually (eventually_gt_nhds (one_div_pos.mpr hμ))).mono fun x hx => ne_of_gt hx
  have hdiff := Kyprianou.Ch05.creepingPotentialDifferenceLimit
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice hPotLim hd
  have herr := hdiff.div hp (ne_of_gt (one_div_pos.mpr hμ))
  simp only [zero_div] at herr
  have heq : (fun x : Real => d + (creepingProbability P Y death x - d * ((U 0) (Set.Ioc x (x + 1))).toReal) / ((U 0) (Set.Ioc x (x + 1))).toReal)
      =ᶠ[atTop] (fun x : Real => creepingProbability P Y death x / ((U 0) (Set.Ioc x (x + 1))).toReal) :=
    hU0.mono fun x hx => by field_simp; ring
  have hsum := (tendsto_const_nhds (x := d)).add herr
  rw [add_zero] at hsum
  exact hsum.congr' heq
