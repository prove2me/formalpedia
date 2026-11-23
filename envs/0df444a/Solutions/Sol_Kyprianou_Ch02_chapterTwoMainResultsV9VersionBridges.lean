-- Prove2me | solution 1 for Kyprianou.Ch02.chapterTwoMainResultsV9VersionBridges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T11:26:34.306723+00:00
-- url     : https://prove2.me/submissions/05cd027d-a36c-485d-9a52-15f2b6ebeb9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV9
import Theorems.Thm_Kyprianou_markedCompoundPoissonRandomMeasureCh02V6
import Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V9
import Theorems.Thm_Kyprianou_poissonRestrictionAndIndependenceGenericCh02V9
import Theorems.Thm_Kyprianou_exercise2_2_AllPartsCh02V6
import Theorems.Thm_Kyprianou_poissonRandomMeasureSupportGenericMeasurableSingletons

set_option autoImplicit false

theorem solution :
    Kyprianou.Ch02.certificateV6_markedCompoundPoissonRandomMeasureCh02V6 ∧
    Kyprianou.Ch02.certificateV9_poissonRandomMeasureExistsGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV9_poissonRestrictionAndIndependenceGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV6_exercise2_2_AllPartsCh02V6 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons :=
  ⟨@Kyprianou.markedCompoundPoissonRandomMeasureCh02V6,
   @Kyprianou.poissonRandomMeasureExistsGenericCh02V9,
   @Kyprianou.poissonRestrictionAndIndependenceGenericCh02V9,
   @Kyprianou.exercise2_2_AllPartsCh02V6,
   @Kyprianou.poissonRandomMeasureSupportGenericMeasurableSingletons⟩
