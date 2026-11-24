-- Prove2me | solution 1 for GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:05.232166+00:00
-- url     : https://prove2.me/submissions/e09e0b7e-c177-41ba-9d69-f02f294a8cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
import Theorems.Thm_GlobalTheory_BI_isChar_linear


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  first | exact @GlobalTheory.BI.isChar_linear | exact GlobalTheory.BI.isChar_linear | (intros; apply GlobalTheory.BI.isChar_linear <;> assumption)
end _root_.GlobalTheory.T
