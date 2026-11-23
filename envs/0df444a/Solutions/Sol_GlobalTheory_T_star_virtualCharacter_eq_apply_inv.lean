-- Prove2me | solution 1 for GlobalTheory.T.star_virtualCharacter_eq_apply_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:37.165598+00:00
-- url     : https://prove2.me/submissions/3f594052-ce65-4746-b297-ad1243dd87d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Theorems.Thm_GlobalTheory_CuspGL_star_virt_eq_inv


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), χ ∈ Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by
  first | exact @GlobalTheory.CuspGL.star_virt_eq_inv | exact GlobalTheory.CuspGL.star_virt_eq_inv | (intros; apply GlobalTheory.CuspGL.star_virt_eq_inv <;> assumption)
end _root_.GlobalTheory.T
