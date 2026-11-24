-- Prove2me | solution 1 for GlobalTheory.BI.isChar_monoidHom_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:12.408313+00:00
-- url     : https://prove2.me/submissions/5fc5b78d-ea64-47fe-89fa-cf0f8105b0a7

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
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI
open Polynomial in
private lemma trace_mulLeft_complex_lemma (z : ℂ) :
    LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ z) = z := by
  have hz : (Algebra.lmul ℂ ℂ z : ℂ →ₗ[ℂ] ℂ) = z • LinearMap.id := by
    ext x
    simp
  rw [hz, map_smul, LinearMap.trace_id]
  simp
end GlobalTheory.BI
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
open Polynomial
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by
  let ρ : Representation ℂ G ℂ :=
    (Algebra.lmul ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp lam)
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G ℂ ρ).1
  convert key using 1
  funext g
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Representation.character]
  exact (trace_mulLeft_complex_lemma _).symm
end _root_.GlobalTheory.BI
end GlobalTheory.BI
