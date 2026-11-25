-- Prove2me | solution 1 for GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:29:12.369823+00:00
-- url     : https://prove2.me/submissions/39ea7a10-3ca4-4429-948d-6c44ad141e65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePowerStatement
import Theorems.Thm_GlobalTheory_BI_mem_virt_of_forall_abByP


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) → ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  first | exact @GlobalTheory.BI.mem_virt_of_forall_abByP | exact GlobalTheory.BI.mem_virt_of_forall_abByP | (intros; apply GlobalTheory.BI.mem_virt_of_forall_abByP <;> assumption)
end _root_.GlobalTheory.T
