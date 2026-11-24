-- Prove2me | solution 1 for GlobalTheory.T.dividedPowerValuations_minVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:04:54.061714+00:00
-- url     : https://prove2.me/submissions/7c4fde58-1d80-410d-98de-47b2100ebbe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesMinPadicValBound
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesMinPadicValBoundStatement
import Theorems.Thm_GlobalTheory_cmValues_minPadicVal_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Formalism.PairingDivisionLocalBalance.MinVal := by
  first | exact @GlobalTheory.cmValues_minPadicVal_bound | exact GlobalTheory.cmValues_minPadicVal_bound | (intros; apply GlobalTheory.cmValues_minPadicVal_bound <;> assumption)
end _root_.GlobalTheory.T
