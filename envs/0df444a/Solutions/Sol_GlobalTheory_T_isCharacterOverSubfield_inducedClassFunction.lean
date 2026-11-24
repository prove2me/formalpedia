-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:23.535473+00:00
-- url     : https://prove2.me/submissions/ccbeaf84-690e-4d7d-ad89-374c2869ff57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunctionStatement
import Theorems.Thm_GlobalTheory_BI_isChar_ind


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (ind H ψ) := by
  first | exact @GlobalTheory.BI.isChar_ind | exact GlobalTheory.BI.isChar_ind | (intros; apply GlobalTheory.BI.isChar_ind <;> assumption)
end _root_.GlobalTheory.T
