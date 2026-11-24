-- Prove2me | solution 1 for Kyprianou.Ch02.chapterTwoMainResultsV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:49:15.426018+00:00
-- url     : https://prove2.me/submissions/98dd369a-068a-407a-b2cc-054920472601

import Mathlib
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists
import Theorems.Thm_Kyprianou_poissonRandomMeasureSupportCountable
import Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
import Theorems.Thm_Kyprianou_sumOfIndependentLevyProcesses
import Theorems.Thm_Kyprianou_compensatedBandIsL2MartingaleCorrected
import Theorems.Thm_Kyprianou_smallJumpLimitCadlagCorrected
import Theorems.Thm_Kyprianou_levyItoDecompositionCorrected
import Theorems.Thm_Kyprianou_boundedVariationCriterionCh02
import Theorems.Thm_Kyprianou_compoundPoissonDriftPathCriterionCh02V3
import Theorems.Thm_Kyprianou_independentSubordinationCh02V3
import Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3
import Theorems.Thm_Kyprianou_markedCompoundPoissonRandomMeasureCh02V5
import Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V3
import Theorems.Thm_Kyprianou_poissonRestrictionAndIndependenceCh02V3
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
import Theorems.Thm_Kyprianou_exercise2_1_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_3_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_4_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_6_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_8_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_11_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V4
import Theorems.Thm_Kyprianou_exercise2_7_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_10_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_5_AllPartsCh02V3
import Theorems.Thm_Kyprianou_exercise2_9_AllPartsCh02V4
import Theorems.Thm_Kyprianou_exercise2_12_AllPartsCh02V4
import Theorems.Thm_Kyprianou_poissonRandomMeasureSupportGenericMeasurableSingletons
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV5
open MeasureTheory ProbabilityTheory Kyprianou
set_option autoImplicit false

theorem solution :
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureExists ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureSupportCountable ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureIntegralLaws ∧
    Kyprianou.Ch02.certificateV2_largeJumpProcessLevy ∧
    Kyprianou.Ch02.certificateV2_sumOfIndependentLevyProcesses ∧
    Kyprianou.Ch02.certificateV2_compensatedBandIsL2Martingale ∧
    Kyprianou.Ch02.certificateV2_smallJumpLimitCadlag ∧
    Kyprianou.Ch02.certificateV2_levyItoDecomposition ∧
    Kyprianou.Ch02.certificateV2_boundedVariationCriterionCh02 ∧
    Kyprianou.Ch02.certificateV3_compoundPoissonDriftPathCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV3_independentSubordinationCh02V3 ∧
    Kyprianou.Ch02.certificateV3_subordinatorCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV4_markedCompoundPoissonRandomMeasureCh02V5 ∧
    Kyprianou.Ch02.certificateV3_poissonRandomMeasureExistsGenericCh02V3 ∧
    Kyprianou.Ch02.certificateV3_poissonRestrictionAndIndependenceCh02V3 ∧
    Kyprianou.Ch02.certificateV3_finiteRegionPoissonIntegralCh02V3 ∧
    Kyprianou.Ch02.certificateV3_compensatedGeneralRegionMartingaleCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_1_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_3_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_4_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_6_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_8_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_11_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_2_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_9_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV4_exercise2_12_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons := by
  exact ⟨
    Kyprianou.poissonRandomMeasureExists,
    Kyprianou.poissonRandomMeasureSupportCountable,
    Kyprianou.poissonRandomMeasureIntegralLaws,
    Kyprianou.largeJumpProcessLevy,
    Kyprianou.sumOfIndependentLevyProcesses,
    Kyprianou.compensatedBandIsL2MartingaleCorrected,
    Kyprianou.smallJumpLimitCadlagCorrected,
    Kyprianou.levyItoDecompositionCorrected,
    Kyprianou.boundedVariationCriterionCh02,
    Kyprianou.compoundPoissonDriftPathCriterionCh02V3,
    Kyprianou.independentSubordinationCh02V3,
    Kyprianou.subordinatorCriterionCh02V3,
    Kyprianou.markedCompoundPoissonRandomMeasureCh02V5,
    Kyprianou.poissonRandomMeasureExistsGenericCh02V3,
    Kyprianou.poissonRestrictionAndIndependenceCh02V3,
    Kyprianou.finiteRegionPoissonIntegralCh02V3,
    Kyprianou.compensatedGeneralRegionMartingaleCh02V3,
    Kyprianou.exercise2_1_AllPartsCh02V3,
    Kyprianou.exercise2_3_AllPartsCh02V3,
    Kyprianou.exercise2_4_AllPartsCh02V3,
    Kyprianou.exercise2_6_AllPartsCh02V3,
    Kyprianou.exercise2_8_AllPartsCh02V3,
    Kyprianou.exercise2_11_AllPartsCh02V3,
    Kyprianou.exercise2_2_AllPartsCh02V4,
    Kyprianou.exercise2_7_AllPartsCh02V3,
    Kyprianou.exercise2_10_AllPartsCh02V3,
    Kyprianou.exercise2_5_AllPartsCh02V3,
    Kyprianou.exercise2_9_AllPartsCh02V4,
    Kyprianou.exercise2_12_AllPartsCh02V4,
    Kyprianou.poissonRandomMeasureSupportGenericMeasurableSingletons
  ⟩
