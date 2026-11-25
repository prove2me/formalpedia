-- Prove2me | solution 1 for GlobalTheory.T.weilRepresentationEtale_of_quadraticField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:36.862843+00:00
-- url     : https://prove2.me/submissions/7efbcefe-3a32-4a7d-b886-649442ce8450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationEtaleOfQuadraticField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationEtaleOfQuadraticFieldStatement
import Theorems.Thm_GlobalTheory_JR_weilEt_of_weilField


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
theorem _root_.solution : WeilField → WeilEt := by
  first | exact @GlobalTheory.JR.weilEt_of_weilField | exact GlobalTheory.JR.weilEt_of_weilField | (intros; apply GlobalTheory.JR.weilEt_of_weilField <;> assumption)
end _root_.GlobalTheory.T
