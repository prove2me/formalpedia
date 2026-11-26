-- Prove2me | solution 1 for Kyprianou.Ch05.potentialRenewalIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:19:19.069807+00:00
-- url     : https://prove2.me/submissions/4628e554-05a8-447b-806c-f1d4ca094d12

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitProbability
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialLaplaceDichotomy
import Theorems.Thm_Kyprianou_Ch05_potentialRenewalOfPositiveLaplace
import Theorems.Thm_Kyprianou_Ch05_potentialRenewalOfZeroMarginals
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Separate the zero process from the strictly positive transform case. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0 := by
  letI := unkilledPotentialUnitProbability P Y death hKilled U hPotential
  rcases unkilledPotentialLaplaceDichotomy P Y death hKilled U hPotential with hzero | hpos
  · exact potentialRenewalOfZeroMarginals P Y death hKilled U hPotential hzero
  · exact potentialRenewalOfPositiveLaplace U hpos
