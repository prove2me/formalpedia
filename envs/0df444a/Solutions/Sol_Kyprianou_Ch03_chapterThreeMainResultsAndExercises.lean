-- Prove2me | solution 1 for Kyprianou.Ch03.chapterThreeMainResultsAndExercises
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:10:07.806046+00:00
-- url     : https://prove2.me/submissions/5aea4959-1207-48d2-b989-3e1d002e928b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_ChapterCertification
import Definitions.Def_Kyprianou_Ch03_ReviewCoreCertification
import Definitions.Def_Kyprianou_Ch03_ExerciseACertification
import Definitions.Def_Kyprianou_Ch03_ExerciseBCertification
import Theorems.Thm_Kyprianou_Ch03_strongMarkovAtExtendedStoppingTime
import Theorems.Thm_Kyprianou_Ch03_quasiLeftContinuousAlongStoppingTimes
import Theorems.Thm_Kyprianou_Ch03_entranceAndHittingAreStoppingTimes
import Theorems.Thm_Kyprianou_Ch03_timeReversalDuality
import Theorems.Thm_Kyprianou_Ch03_supremumInfimumDuality
import Theorems.Thm_Kyprianou_Ch03_exponentialMomentsIffLargeJumpIntegral
import Theorems.Thm_Kyprianou_Ch03_submultiplicativeMomentsIffLargeJumpIntegral
import Theorems.Thm_Kyprianou_Ch03_esscherChangeOfMeasurePreservesLevyAndTriplet
import Theorems.Thm_Kyprianou_Ch03_esscherOfSpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_esscherDensityAtExtendedStoppingTime
import Theorems.Thm_Kyprianou_Ch03_upwardFirstPassageLaplaceTransform
import Theorems.Thm_Kyprianou_Ch03_upwardPassageProbabilityAndDrift
import Theorems.Thm_Kyprianou_Ch03_upwardPassageIsKilledSubordinator
import Theorems.Thm_Kyprianou_Ch03_esscherExponentialDensityConsistent
import Theorems.Thm_Kyprianou_Ch03_esscherFiniteHorizonMeasures
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegativeLevyCadlagModification
import Theorems.Thm_Kyprianou_Ch03_upwardPassageZeroRootRightSlopeCriterion
import Theorems.Thm_Kyprianou_Ch03_esscherCanonicalGlobalExtension
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Theorems.Thm_Kyprianou_Ch03_exercise32ReflectionsStrongMarkov
import Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExponentialEnvelope
import Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExamples
import Theorems.Thm_Kyprianou_Ch03_exercise33StableFractionalMomentCriterion
import Theorems.Thm_Kyprianou_Ch03_exercise34TemperedStableDecomposition
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch03_exercise36SupremumAtIndependentExponentialTime
import Theorems.Thm_Kyprianou_Ch03_exercise37PositiveStableLaplaceAndVariation
import Theorems.Thm_Kyprianou_Ch03_exercise34TemperedStableComponentRegimes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch03


theorem solution :
  certificate_3_1 ∧
  certificate_3_2 ∧
  certificate_3_3 ∧
  certificate_3_4 ∧
  certificate_3_5 ∧
  certificate_3_6 ∧
  certificate_3_8 ∧
  certificate_3_9 ∧
  certificate_3_10 ∧
  certificate_3_11 ∧
  certificate_3_12 ∧
  certificate_3_13 ∧
  certificate_3_14 ∧
  reviewCoreCertification ∧
  exerciseGroupACertification ∧
  exerciseGroupBCertification := by
  exact ⟨
    Kyprianou.Ch03.strongMarkovAtExtendedStoppingTime,
    Kyprianou.Ch03.quasiLeftContinuousAlongStoppingTimes,
    Kyprianou.Ch03.entranceAndHittingAreStoppingTimes,
    Kyprianou.Ch03.timeReversalDuality,
    Kyprianou.Ch03.supremumInfimumDuality,
    Kyprianou.Ch03.exponentialMomentsIffLargeJumpIntegral,
    Kyprianou.Ch03.submultiplicativeMomentsIffLargeJumpIntegral,
    Kyprianou.Ch03.esscherChangeOfMeasurePreservesLevyAndTriplet,
    Kyprianou.Ch03.esscherOfSpectrallyNegativeLevy,
    Kyprianou.Ch03.esscherDensityAtExtendedStoppingTime,
    Kyprianou.Ch03.upwardFirstPassageLaplaceTransform,
    Kyprianou.Ch03.upwardPassageProbabilityAndDrift,
    Kyprianou.Ch03.upwardPassageIsKilledSubordinator,
      ⟨Kyprianou.Ch03.esscherExponentialDensityConsistent, Kyprianou.Ch03.esscherFiniteHorizonMeasures, Kyprianou.Ch03.spectrallyNegativeLevyCadlagModification, Kyprianou.Ch03.upwardPassageZeroRootRightSlopeCriterion, Kyprianou.Ch03.esscherCanonicalGlobalExtension⟩,
      ⟨Kyprianou.Ch03.completedNaturalLevyFiltrationRightContinuous, Kyprianou.Ch03.exercise32ReflectionsStrongMarkov, Kyprianou.Ch03.exercise33SubmultiplicativeExponentialEnvelope, Kyprianou.Ch03.exercise33SubmultiplicativeExamples, Kyprianou.Ch03.exercise33StableFractionalMomentCriterion⟩,
      ⟨Kyprianou.Ch03.exercise34TemperedStableDecomposition, Kyprianou.Ch03.exercise35LaplaceExponentRegularity, Kyprianou.Ch03.exercise36SupremumAtIndependentExponentialTime, Kyprianou.Ch03.exercise37PositiveStableLaplaceAndVariation, Kyprianou.Ch03.exercise34TemperedStableComponentRegimes⟩
  ⟩

