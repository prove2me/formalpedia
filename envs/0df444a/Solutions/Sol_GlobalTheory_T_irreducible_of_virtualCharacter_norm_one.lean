-- Prove2me | solution 1 for GlobalTheory.T.irreducible_of_virtualCharacter_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:19.149149+00:00
-- url     : https://prove2.me/submissions/5fae9364-b166-40ca-9bf2-42675d6403e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Theorems.Thm_GlobalTheory_BI_irr_of_norm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  first | exact @GlobalTheory.BI.irr_of_norm_one | exact GlobalTheory.BI.irr_of_norm_one | (intros; apply GlobalTheory.BI.irr_of_norm_one <;> assumption)
end _root_.GlobalTheory.T
