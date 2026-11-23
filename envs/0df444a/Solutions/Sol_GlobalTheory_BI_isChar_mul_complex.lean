-- Prove2me | solution 1 for GlobalTheory.BI.isChar_mul_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:47.555806+00:00
-- url     : https://prove2.me/submissions/f5b958fc-243f-4002-848a-e1cba2f9acab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
open Polynomial
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by
  obtain ⟨n, ρ, hρ⟩ := ha
  obtain ⟨m, σ, hσ⟩ := hb
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (Representation.tprod ρ σ)).1
  convert key using 1
  funext g
  simp [Representation.char_tensor, hρ, hσ]
end _root_.GlobalTheory.BI
end GlobalTheory.BI
