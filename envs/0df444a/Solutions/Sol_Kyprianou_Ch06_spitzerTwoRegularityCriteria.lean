-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerTwoRegularityCriteria
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:22:47.195214+00:00
-- url     : https://prove2.me/submissions/625893ab-a0b2-4763-915d-0ac7ef784cb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Theorems.Thm_Kyprianou_Ch06_spitzerOpenRegularityCriterion
import Theorems.Thm_Kyprianou_Ch06_spitzerClosedRegularityCriterion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch06

/-- Exercise 6.8: both the strict and non-strict positive-time
entrance tests, including their distinct probability integrands. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X) :
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) ∧
    (IsRegularFor P X 0 (Set.Ici 0) ↔
      NonnegativeOccupationDiverges P X) := by
  constructor
  · exact spitzerOpenRegularityCriterion P X hX hNotSubordinator
  · exact spitzerClosedRegularityCriterion P X hX hNotSubordinator

