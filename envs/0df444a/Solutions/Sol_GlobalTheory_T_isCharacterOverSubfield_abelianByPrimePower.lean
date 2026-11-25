-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:57.078571+00:00
-- url     : https://prove2.me/submissions/2f32cd15-9517-40ee-b6cf-21280745a91b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePowerStatement
import Theorems.Thm_GlobalTheory_BI_isChar_of_abByP


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_abByP | exact GlobalTheory.BI.isChar_of_abByP | (intros; apply GlobalTheory.BI.isChar_of_abByP <;> assumption)
end _root_.GlobalTheory.T
