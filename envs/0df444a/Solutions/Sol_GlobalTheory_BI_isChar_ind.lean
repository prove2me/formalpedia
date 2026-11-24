-- Prove2me | solution 1 for GlobalTheory.BI.isChar_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:41.281798+00:00
-- url     : https://prove2.me/submissions/ee51e73c-a0e1-42ef-bdf4-7a22949ff3be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Theorems.Thm_GlobalTheory_T_inducedClassFunctionFromSubgroup_eq_finsum_cosets
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_restrict_classFunction_one
import Theorems.Thm_GlobalTheory_T_isCharacter_finsum_conj_subgroupFunctionExtendByZero


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L),
    IsChar K L ψ → IsChar K L (ind H ψ) := by
  intro K L _ _ _ _ _ G _ _ H ψ h
  have hcl : ∀ a x : H, ψ (x⁻¹ * a * x) = ψ a := (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one K L H ψ h).2.1
  have e : ind H ψ = fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) :=
    funext (GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets L G H ψ hcl)
  rw [e]
  exact GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero K L G H ψ h
end GlobalTheory.BI
