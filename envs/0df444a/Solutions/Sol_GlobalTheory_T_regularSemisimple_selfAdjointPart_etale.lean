-- Prove2me | solution 1 for GlobalTheory.T.regularSemisimple_selfAdjointPart_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:34:02.628707+00:00
-- url     : https://prove2.me/submissions/efe72570-b74b-49c4-b765-f86f9eb2293d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleSelfAdjointPartEtale
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleSelfAdjointPartEtaleStatement
import Theorems.Thm_GlobalTheory_RegSS_plusEtale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.RegSS.PlusEtale := by
  first | exact @GlobalTheory.RegSS.plusEtale | exact GlobalTheory.RegSS.plusEtale | (intros; apply GlobalTheory.RegSS.plusEtale <;> assumption)
end _root_.GlobalTheory.T
