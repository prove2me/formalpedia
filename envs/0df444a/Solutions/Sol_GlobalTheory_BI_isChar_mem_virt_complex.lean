-- Prove2me | solution 1 for GlobalTheory.BI.isChar_mem_virt_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:41.449051+00:00
-- url     : https://prove2.me/submissions/c2ad2869-8f3f-461e-86c5-ac5672f4cddd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear

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
theorem _root_.solution {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
  AddSubgroup.subset_closure h
end _root_.GlobalTheory.BI
end GlobalTheory.BI
