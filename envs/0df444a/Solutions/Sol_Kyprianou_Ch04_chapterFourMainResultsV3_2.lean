-- Prove2me | solution 2 for Kyprianou.Ch04.chapterFourMainResultsV3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-26T02:50:22.586273+00:00
-- url     : https://prove2.me/submissions/d0e44095-2a6b-4c92-9127-be0b0943f738
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_CompensationCertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_4Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_5Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Theorems.Thm_Kyprianou_Ch04_totalIdleTimeTrafficRegimesV2
import Theorems.Thm_Kyprianou_Ch04_boundedVariationChangeOfVariables
import Theorems.Thm_Kyprianou_Ch04_generalLevyItoFormulaV2
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_conditionalPredictableCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_compensatedJumpIntegralTrueMartingaleAdaptedV2
import Theorems.Thm_Kyprianou_Ch04_kellaWhittTrueMartingale
import Theorems.Thm_Kyprianou_Ch04_exponentialTimeReflectedInfimumTransform
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdownTransformAndDrift
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricConvolutionV2
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Theorems.Thm_Kyprianou_Ch04_downwardFirstPassageUndershootLaw
import Theorems.Thm_Kyprianou_Ch04_exercise_4_1_completeV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_2_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_4_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_6_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_7_complete
import Theorems.Thm_Kyprianou_Ch04_exercise_4_8_completeV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_9_complete

set_option autoImplicit false

open Kyprianou.Ch04

/-- Cumulative Chapter 4 capstone: every numbered source result. -/
theorem solution :
    certificate_4_1_v2 ∧
    certificate_4_2_v2 ∧
    certificate_4_3_v2 ∧
    certificate_4_4_v3 ∧
    certificate_4_5_v3 ∧
    certificate_4_6_v3 ∧
    certificate_4_7_v2 ∧
    certificate_4_8_v2 ∧
    certificate_4_9_v2 ∧
    certificate_4_10_v2 ∧
    certificate_4_11_v2 ∧
    certificate_4_12_v2 ∧
    certificate_exercise_4_1_v2 ∧
    certificate_exercise_4_2 ∧
    certificate_exercise_4_3 ∧
    certificate_exercise_4_4 ∧
    certificate_exercise_4_5 ∧
    certificate_exercise_4_6 ∧
    certificate_exercise_4_7 ∧
    certificate_exercise_4_8_v2 ∧
    certificate_exercise_4_9 := by
  exact ⟨
    Kyprianou.Ch04.totalIdleTimeTrafficRegimesV2,
    Kyprianou.Ch04.boundedVariationChangeOfVariables,
    Kyprianou.Ch04.generalLevyItoFormulaV2,
    Kyprianou.Ch04.nonnegativePredictableJumpCompensationCommonNullV2,
    Kyprianou.Ch04.conditionalPredictableCompensationCommonNullV2,
    Kyprianou.Ch04.compensatedJumpIntegralTrueMartingaleAdaptedV2,
    Kyprianou.Ch04.kellaWhittTrueMartingale,
    Kyprianou.Ch04.exponentialTimeReflectedInfimumTransform,
    Kyprianou.Ch04.limitingDrawdownTransformAndDrift,
    Kyprianou.Ch04.stationaryWorkloadGeometricConvolutionV2,
    Kyprianou.Ch04.smallTimeDriftLimit,
    Kyprianou.Ch04.downwardFirstPassageUndershootLaw,
    Kyprianou.Ch04.exercise_4_1_completeV2,
    Kyprianou.Ch04.exercise_4_2_complete,
    Kyprianou.Ch04.exercise_4_3_complete,
    Kyprianou.Ch04.exercise_4_4_complete,
    Kyprianou.Ch04.exercise_4_5_complete,
    Kyprianou.Ch04.exercise_4_6_complete,
    Kyprianou.Ch04.exercise_4_7_complete,
    Kyprianou.Ch04.exercise_4_8_completeV2,
    Kyprianou.Ch04.exercise_4_9_complete
  ⟩
