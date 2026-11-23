-- Prove2me | solution 1 for GlobalTheory.IrrPi.irr_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:53.772948+00:00
-- url     : https://prove2.me/submissions/757f6a71-68a5-4b98-b459-3f27d7e191cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProduct
import Theorems.Thm_GlobalTheory_IrrPi_isChar_of_irr
import Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.IrrPi
namespace GlobalTheory.IrrPi
theorem _root_.solution {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, n ≠ 0 ∧ χ 1 = n := by
  obtain ⟨n, hn, h0⟩ := (isChar_restrict_conj_one ℂ ℂ G χ (isChar_of_irr h)).2.2
  refine ⟨n, fun h1 => ?_, hn⟩
  have := pair_self_of_isIrrChar_algClosed ℂ G χ h
  rw [h0 h1] at this
  simp [pair] at this
end GlobalTheory.IrrPi
