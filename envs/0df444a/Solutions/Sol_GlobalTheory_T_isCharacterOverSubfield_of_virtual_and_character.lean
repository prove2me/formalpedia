-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:59.401734+00:00
-- url     : https://prove2.me/submissions/e9239fb7-2276-4ffe-b3b7-d131cd05df35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacterStatement
import Theorems.Thm_GlobalTheory_BI_isChar_of_isChar_of_mem_virt


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_isChar_of_mem_virt | exact GlobalTheory.BI.isChar_of_isChar_of_mem_virt | (intros; apply GlobalTheory.BI.isChar_of_isChar_of_mem_virt <;> assumption)
end _root_.GlobalTheory.T
