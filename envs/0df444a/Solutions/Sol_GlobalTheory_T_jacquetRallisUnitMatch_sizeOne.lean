-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:55.355564+00:00
-- url     : https://prove2.me/submissions/b357b296-d113-4776-84c9-178d1d563a1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisUnitMatchSizeOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisUnitMatchSizeOneStatement
import Theorems.Thm_GlobalTheory_JR_SizeOne_unitMatch_zero


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
theorem _root_.solution : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
end _root_.GlobalTheory.T
