-- Prove2me | solution 1 for GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:26:07.941837+00:00
-- url     : https://prove2.me/submissions/ce668805-f757-4a9f-8172-5a3ca711af4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSupp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement
import Theorems.Thm_GlobalTheory_JR_UnitTest_unitG_isTest


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by
  first | exact @GlobalTheory.JR.UnitTest.unitG_isTest | exact GlobalTheory.JR.UnitTest.unitG_isTest | (intros; apply GlobalTheory.JR.UnitTest.unitG_isTest <;> assumption)
end _root_.GlobalTheory.T
