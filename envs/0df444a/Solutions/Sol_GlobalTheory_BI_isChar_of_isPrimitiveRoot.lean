-- Prove2me | solution 1 for GlobalTheory.BI.isChar_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:08.514023+00:00
-- url     : https://prove2.me/submissions/ccefafef-eafe-4326-90fb-d37424e105bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharOfIsPrimitiveRoot
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_abelianByPrimePower
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_of_virtual_and_character
import Theorems.Thm_GlobalTheory_T_mem_virtualCharacters_of_abelianByPrimePower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ G _ _ hG χ hχ
  refine GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character K L G χ hχ (GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower K L G (fun H hH ψ hψ => ?_) χ hχ)
  exact GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower K L m ζ hm hζ H (fun h => Subtype.ext (by simpa using hG (h : G))) hH ψ hψ
end GlobalTheory.BI
