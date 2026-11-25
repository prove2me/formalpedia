-- Prove2me | solution 1 for GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:48.957909+00:00
-- url     : https://prove2.me/submissions/df24ec22-9e67-438a-912b-265420f0c1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAddStatement
import Theorems.Thm_GlobalTheory_BI_exists_irrChar_add


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  first | exact @GlobalTheory.BI.exists_irrChar_add | exact GlobalTheory.BI.exists_irrChar_add | (intros; apply GlobalTheory.BI.exists_irrChar_add <;> assumption)
end _root_.GlobalTheory.T
