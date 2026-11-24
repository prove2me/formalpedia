-- Prove2me | solution 1 for GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:06.004978+00:00
-- url     : https://prove2.me/submissions/2cbacd71-f3de-4c09-b4bd-7005ba1c7675

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement
import Theorems.Thm_GlobalTheory_BI_isChar_finsum_conj_ext0_of_isChar


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  first | exact @GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | exact GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | (intros; apply GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar <;> assumption)
end _root_.GlobalTheory.T
