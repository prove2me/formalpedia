-- Prove2me | solution 1 for Kyprianou.Ch06.chapterSixMainResults
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:32:38.473042+00:00
-- url     : https://prove2.me/submissions/42cae682-ec0d-4859-bc8c-69a05c8b7b73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_positiveHalfLineRegularityClassification
import Theorems.Thm_Kyprianou_Ch06_onlyCompoundPoissonHasClosedNotOpenRegularity
import Theorems.Thm_Kyprianou_Ch06_continuousOrMarkedLocalTimeAtMaximum
import Theorems.Thm_Kyprianou_Ch06_maximumOccupationCoefficientCriterion
import Theorems.Thm_Kyprianou_Ch06_inverseLocalTimeStoppingTimes
import Theorems.Thm_Kyprianou_Ch06_ascendingLadderSubordinatorDichotomy
import Theorems.Thm_Kyprianou_Ch06_ascendingLadderTimeDrift
import Theorems.Thm_Kyprianou_Ch06_excursionPointProcessWithPossibleKilling
import Theorems.Thm_Kyprianou_Ch06_wienerHopfFactorisationAllFourParts
import Theorems.Thm_Kyprianou_Ch06_exponentialSampledVectorLevyIsInfinitelyDivisible
import Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonPointArrivalAndIndependence
import Theorems.Thm_Kyprianou_Ch06_uniquenessOfAdmissibleWienerHopfFactors
import Theorems.Thm_Kyprianou_Ch06_stableExamplesOfBoundedVariationZeroDriftRegularity
import Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeUnboundedVariationFirstPassage
import Theorems.Thm_Kyprianou_Ch06_exponentialAndGeometricKillingOfCompoundPoissonAgree
import Theorems.Thm_Kyprianou_Ch06_compoundPoissonOfBothExtremalOccupations
import Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeDescendingLadderHeightTriplet
import Theorems.Thm_Kyprianou_Ch06_spectrallyNegativeStablePositivityAndSupremum
import Theorems.Thm_Kyprianou_Ch06_secondWienerHopfFactorisationIdentity
import Theorems.Thm_Kyprianou_Ch06_spitzerTwoRegularityCriteria
import Theorems.Thm_Kyprianou_Ch06_geometricTimeRandomWalkWienerHopfFiveParts
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_5
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_6
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_7
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_8
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_9
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_10
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_11
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_15
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_16
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_17
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_18
import Definitions.Def_Kyprianou_Ch06_certificate_result_6_19
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_1
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_2
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_3
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_4
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_5
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_6
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_7
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_8
import Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_9
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Kyprianou.Ch06

theorem solution :
  certificate_result_6_5 ∧
  certificate_result_6_6 ∧
  certificate_result_6_7 ∧
  certificate_result_6_8 ∧
  certificate_result_6_9 ∧
  certificate_result_6_10 ∧
  certificate_result_6_11 ∧
  certificate_result_6_15 ∧
  certificate_result_6_16 ∧
  certificate_result_6_17 ∧
  certificate_result_6_18 ∧
  certificate_result_6_19 ∧
  certificate_exercise_6_1 ∧
  certificate_exercise_6_2 ∧
  certificate_exercise_6_3 ∧
  certificate_exercise_6_4 ∧
  certificate_exercise_6_5 ∧
  certificate_exercise_6_6 ∧
  certificate_exercise_6_7 ∧
  certificate_exercise_6_8 ∧
  certificate_exercise_6_9 := by
  exact ⟨Kyprianou.Ch06.positiveHalfLineRegularityClassification,
    Kyprianou.Ch06.onlyCompoundPoissonHasClosedNotOpenRegularity,
    Kyprianou.Ch06.continuousOrMarkedLocalTimeAtMaximum,
    Kyprianou.Ch06.maximumOccupationCoefficientCriterion,
    Kyprianou.Ch06.inverseLocalTimeStoppingTimes,
    Kyprianou.Ch06.ascendingLadderSubordinatorDichotomy,
    Kyprianou.Ch06.ascendingLadderTimeDrift,
    Kyprianou.Ch06.excursionPointProcessWithPossibleKilling,
    Kyprianou.Ch06.wienerHopfFactorisationAllFourParts,
    Kyprianou.Ch06.exponentialSampledVectorLevyIsInfinitelyDivisible,
    Kyprianou.Ch06.firstMarkedPoissonPointArrivalAndIndependence,
    Kyprianou.Ch06.uniquenessOfAdmissibleWienerHopfFactors,
    Kyprianou.Ch06.stableExamplesOfBoundedVariationZeroDriftRegularity,
    Kyprianou.Ch06.spectrallyNegativeUnboundedVariationFirstPassage,
    Kyprianou.Ch06.exponentialAndGeometricKillingOfCompoundPoissonAgree,
    Kyprianou.Ch06.compoundPoissonOfBothExtremalOccupations,
    Kyprianou.Ch06.spectrallyNegativeDescendingLadderHeightTriplet,
    Kyprianou.Ch06.spectrallyNegativeStablePositivityAndSupremum,
    Kyprianou.Ch06.secondWienerHopfFactorisationIdentity,
    Kyprianou.Ch06.spitzerTwoRegularityCriteria,
    Kyprianou.Ch06.geometricTimeRandomWalkWienerHopfFiveParts⟩
