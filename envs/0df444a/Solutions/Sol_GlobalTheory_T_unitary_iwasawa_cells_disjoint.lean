-- Prove2me | solution 1 for GlobalTheory.T.unitary_iwasawa_cells_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:04.786123+00:00
-- url     : https://prove2.me/submissions/7724b5b2-de3b-4afd-b65a-4f1119c838a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjointStatement
import Theorems.Thm_GlobalTheory_InertZeta_cosetInj


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
theorem _root_.solution : CosetInj := by
  first | exact @GlobalTheory.InertZeta.cosetInj | exact GlobalTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.InertZeta.cosetInj <;> assumption)
end _root_.GlobalTheory.T
