-- Prove2me | solution 1 for Kyprianou.Ch02.chapterTwoMainResultsV9
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T10:33:13.600343+00:00
-- url     : https://prove2.me/submissions/95cbeb9d-339b-4f98-8f44-a05c2002e1da

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV9
import Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV5
import Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV9VersionBridges
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
    Kyprianou.Ch02.certificateV6_markedCompoundPoissonRandomMeasureCh02V6 ∧
    Kyprianou.Ch02.certificateV9_poissonRandomMeasureExistsGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV9_poissonRestrictionAndIndependenceGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV3_finiteRegionPoissonIntegralCh02V3 ∧
    Kyprianou.Ch02.certificateV3_compensatedGeneralRegionMartingaleCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_1_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_3_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_4_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_6_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_8_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_11_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV6_exercise2_2_AllPartsCh02V6 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_9_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV4_exercise2_12_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons
 := by
  rcases Kyprianou.Ch02.chapterTwoMainResultsV5 with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, _, _, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, _⟩
  rcases Kyprianou.Ch02.chapterTwoMainResultsV9VersionBridges with ⟨h13, h14', h15', h23', h30'⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14', h15', h16, h17, h18, h19, h20, h21, h22, h23, h23', h25, h26, h27, h28, h29, h30'⟩
