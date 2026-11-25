-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_induction_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:41.513124+00:00
-- url     : https://prove2.me/submissions/e766e007-be10-4341-93f3-9cc29ca2e31b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Theorems.Thm_GlobalTheory_BI_isChar_induction


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (Q : (G → L) → Prop), Q 0 → (∀ φ c : G → L, IsIrrChar K L φ → IsChar K L c → Q c → Q (φ + c)) → ∀ a : G → L, IsChar K L a → Q a := by
  first | exact @GlobalTheory.BI.isChar_induction | exact GlobalTheory.BI.isChar_induction | (intros; apply GlobalTheory.BI.isChar_induction <;> assumption)
end _root_.GlobalTheory.T
