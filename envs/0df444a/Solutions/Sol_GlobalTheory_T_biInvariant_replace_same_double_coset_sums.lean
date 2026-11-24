-- Prove2me | solution 1 for GlobalTheory.T.biInvariant_replace_same_double_coset_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:51.308209+00:00
-- url     : https://prove2.me/submissions/7001996d-f687-4f88-b72c-64fd4e01f334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSumsStatement
import Theorems.Thm_GlobalTheory_InertZeta_dosetSwap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : DosetSwap := by
  first | exact @GlobalTheory.InertZeta.dosetSwap | exact GlobalTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.InertZeta.dosetSwap <;> assumption)
end _root_.GlobalTheory.T
