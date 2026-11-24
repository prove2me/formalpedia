-- Prove2me | solution 1 for GlobalTheory.T.mem_virtualCharacters_iff_sub_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:27.712844+00:00
-- url     : https://prove2.me/submissions/ad3e422b-a1f4-479f-913b-3772a27d8b22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharactersStatement
import Theorems.Thm_GlobalTheory_BI_mem_virt_iff_sub


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L), f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  first | exact @GlobalTheory.BI.mem_virt_iff_sub | exact GlobalTheory.BI.mem_virt_iff_sub | (intros; apply GlobalTheory.BI.mem_virt_iff_sub <;> assumption)
end _root_.GlobalTheory.T
