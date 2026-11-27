-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorPotentialRenewalLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:21:20.454959+00:00
-- url     : https://prove2.me/submissions/ff10dba7-6223-48ef-a271-4f58d4ee57e6

import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitProbability
import Theorems.Thm_Kyprianou_Ch05_potentialRenewalIdentity
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitMeanV1
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitSupportV1
import Theorems.Thm_Kyprianou_Ch05_renewalPotentialSubtractOriginV1
import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05

/-- Transfer classical renewal limits to the undiscounted potential. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P) :
  let mu : Real := ∫ omega, Y 1 omega ∂P
  ((NonLatticeMeasure (U 0) →
    ∀ y : Real, 0 < y →
      Tendsto
        (fun x : Real =>
          ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / mu))) ∧
   (Tendsto
     (fun x : Real =>
       ((U 0) (Set.Icc (0 : Real) x)).toReal / x)
     atTop (nhds (1 / mu))))
 := by
  letI := unkilledPotentialUnitProbability P Y death hKilled U hPotential
  have hm := unkilledPotentialUnitMeanV1 P Y death hKilled U hPotential hFiniteMean
  have hs := unkilledPotentialUnitSupportV1 P Y death hKilled U hPotential
  have hr := potentialRenewalIdentity P Y death hKilled U hPotential
  have hp : 0 < ∫ x : Real, x ∂(U 1) := hm.2.symm ▸ hPositiveMean
  have ht := renewalPotentialSubtractOriginV1 (U 1) (U 0)
    hs.1 hm.1 hp hr hs.2
  dsimp only at ht ⊢
  rwa [hm.2] at ht
