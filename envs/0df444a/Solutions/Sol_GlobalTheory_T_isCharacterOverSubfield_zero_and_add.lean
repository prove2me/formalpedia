-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_zero_and_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:03.07316+00:00
-- url     : https://prove2.me/submissions/69b055a0-0763-4a52-bde9-9910b2fc8268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAddStatement
import Theorems.Thm_GlobalTheory_BI_isChar_zero_and_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G], IsChar K L (0 : G → L) ∧ ∀ a b : G → L, IsChar K L a → IsChar K L b → IsChar K L (a + b) := by
  first | exact @GlobalTheory.BI.isChar_zero_and_add | exact GlobalTheory.BI.isChar_zero_and_add | (intros; apply GlobalTheory.BI.isChar_zero_and_add <;> assumption)
end _root_.GlobalTheory.T
