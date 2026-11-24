-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_block_diagonal_levi_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:14.90141+00:00
-- url     : https://prove2.me/submissions/9885e9fe-2c8b-45a4-9ff7-43e80c486c5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnitaryBlockDiagonalLeviElement
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnitaryBlockDiagonalLeviElementStatement
import Theorems.Thm_GlobalTheory_InertZeta_leviExists


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
theorem _root_.solution : LeviExists := by
  first | exact @GlobalTheory.InertZeta.leviExists | exact GlobalTheory.InertZeta.leviExists | (intros; apply GlobalTheory.InertZeta.leviExists <;> assumption)
end _root_.GlobalTheory.T
