-- Prove2me | solution 1 for Kyprianou.Ch07.chapterSevenMainResults
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:08:35.521489+00:00
-- url     : https://prove2.me/submissions/5190bfda-1073-4fe6-bf22-55e6dfe26dc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_1
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_2
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_4
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_5
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_6
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_7
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_8
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_9
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_10
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_11
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_12
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_13
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_14
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_15
import Definitions.Def_Kyprianou_Ch07_certificate_result_7_16
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_1
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_2
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_3
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_4
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_5
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_6
import Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_7
import Theorems.Thm_Kyprianou_Ch07_driftingOscillatingIntegralTrichotomy
import Theorems.Thm_Kyprianou_Ch07_driftingOscillatingLevyMeasureCriterion
import Theorems.Thm_Kyprianou_Ch07_portStoneFourierTransienceCriterion
import Theorems.Thm_Kyprianou_Ch07_pathwiseTransienceRecurrenceCharacterisation
import Theorems.Thm_Kyprianou_Ch07_cramerExponentialRuinAsymptotic
import Theorems.Thm_Kyprianou_Ch07_quintupleFirstPassageLaw
import Theorems.Thm_Kyprianou_Ch07_vigonAscendingLadderJumpTail
import Theorems.Thm_Kyprianou_Ch07_spectrallyPositiveAscendingLadderJumpTail
import Theorems.Thm_Kyprianou_Ch07_upwardCreepingLadderDrift
import Theorems.Thm_Kyprianou_Ch07_upwardCreepingLevyTripletCriterion
import Theorems.Thm_Kyprianou_Ch07_pointHittingFourierCriterion
import Theorems.Thm_Kyprianou_Ch07_regularlyVaryingConvolutionTails
import Theorems.Thm_Kyprianou_Ch07_kestenBoundSubexponentialConvolution
import Theorems.Thm_Kyprianou_Ch07_infinitelyDivisibleRegularlyVaryingTail
import Theorems.Thm_Kyprianou_Ch07_heavyTailRuinAsymptoticAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_1SupremumMomentsAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_2StrongLawAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_3SpectrallyNegativeWienerHopfAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_4StablePassageAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_5BivariateAscendingLadderJumpMeasure
import Theorems.Thm_Kyprianou_Ch07_exercise7_6CreepingHittingAllParts
import Theorems.Thm_Kyprianou_Ch07_exercise7_7RogozinTwoSidedExitAllParts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Kyprianou.Ch07

theorem solution :
  certificate_result_7_1 ∧
  certificate_result_7_2 ∧
  certificate_result_7_4 ∧
  certificate_result_7_5 ∧
  certificate_result_7_6 ∧
  certificate_result_7_7 ∧
  certificate_result_7_8 ∧
  certificate_result_7_9 ∧
  certificate_result_7_10 ∧
  certificate_result_7_11 ∧
  certificate_result_7_12 ∧
  certificate_result_7_13 ∧
  certificate_result_7_14 ∧
  certificate_result_7_15 ∧
  certificate_result_7_16 ∧
  certificate_exercise_7_1 ∧
  certificate_exercise_7_2 ∧
  certificate_exercise_7_3 ∧
  certificate_exercise_7_4 ∧
  certificate_exercise_7_5 ∧
  certificate_exercise_7_6 ∧
  certificate_exercise_7_7 := by
  exact ⟨
    Kyprianou.Ch07.driftingOscillatingIntegralTrichotomy,
    Kyprianou.Ch07.driftingOscillatingLevyMeasureCriterion,
    Kyprianou.Ch07.portStoneFourierTransienceCriterion,
    Kyprianou.Ch07.pathwiseTransienceRecurrenceCharacterisation,
    Kyprianou.Ch07.cramerExponentialRuinAsymptotic,
    Kyprianou.Ch07.quintupleFirstPassageLaw,
    Kyprianou.Ch07.vigonAscendingLadderJumpTail,
    Kyprianou.Ch07.spectrallyPositiveAscendingLadderJumpTail,
    Kyprianou.Ch07.upwardCreepingLadderDrift,
    Kyprianou.Ch07.upwardCreepingLevyTripletCriterion,
    Kyprianou.Ch07.pointHittingFourierCriterion,
    Kyprianou.Ch07.regularlyVaryingConvolutionTails,
    Kyprianou.Ch07.kestenBoundSubexponentialConvolution,
    Kyprianou.Ch07.infinitelyDivisibleRegularlyVaryingTail,
    Kyprianou.Ch07.heavyTailRuinAsymptoticAllParts,
    Kyprianou.Ch07.exercise7_1SupremumMomentsAllParts,
    Kyprianou.Ch07.exercise7_2StrongLawAllParts,
    Kyprianou.Ch07.exercise7_3SpectrallyNegativeWienerHopfAllParts,
    Kyprianou.Ch07.exercise7_4StablePassageAllParts,
    Kyprianou.Ch07.exercise7_5BivariateAscendingLadderJumpMeasure,
    Kyprianou.Ch07.exercise7_6CreepingHittingAllParts,
    Kyprianou.Ch07.exercise7_7RogozinTwoSidedExitAllParts
  ⟩
