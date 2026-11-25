-- Prove2me | solution 1 for GlobalTheory.T.blockValue_on_rows_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:14.142078+00:00
-- url     : https://prove2.me/submissions/67bf71da-f318-4ed8-879f-c19717627dc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Theorems.Thm_GlobalTheory_blockValue_rows


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : BiValue := by
  first | exact @GlobalTheory.blockValue_rows | exact GlobalTheory.blockValue_rows | (intros; apply GlobalTheory.blockValue_rows <;> assumption)
end _root_.GlobalTheory.T
