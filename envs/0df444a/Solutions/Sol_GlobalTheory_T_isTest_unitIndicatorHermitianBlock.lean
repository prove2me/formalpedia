-- Prove2me | solution 1 for GlobalTheory.T.isTest_unitIndicatorHermitianBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:15:59.230969+00:00
-- url     : https://prove2.me/submissions/2ab31b35-66bd-4d6a-812a-e559523161df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsTestUnitIndicatorHermitianBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsTestUnitIndicatorHermitianBlockStatement
import Theorems.Thm_GlobalTheory_JR_isTest_unitU


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
end _root_.GlobalTheory.T
