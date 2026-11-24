-- Prove2me | solution 1 for GlobalTheory.BI.virt_mul_comap_conj_ind_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:41:21.625055+00:00
-- url     : https://prove2.me/submissions/6a770601-9921-46d4-934b-f35a3d493d69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_BI_isChar_mul_complex
import Theorems.Thm_GlobalTheory_BI_isChar_monoidHom_complex
import Theorems.Thm_GlobalTheory_BI_isChar_ind
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
open GlobalTheory GlobalTheory.BI
open Polynomial
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G],
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G,
      a * b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G),
      (fun h => a (f h)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧
    (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H →
      _root_.GlobalTheory.BI.ind H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  intro G _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb' => exact AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_mul_complex ha' hb')
      | zero => simpa using zero_mem _
      | add b c _ _ hb hc => simpa [mul_add] using add_mem hb hc
      | neg b _ hb => simpa [mul_neg] using neg_mem hb
    | zero => simpa using zero_mem _
    | add a c _ _ ha hc => simpa [add_mul] using add_mem ha hc
    | neg a _ ha => simpa [neg_mul] using neg_mem ha
  · intro a ha H _ f
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      exact AddSubgroup.subset_closure
        ((_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').1 H f)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | neg a _ ha => exact neg_mem ha
  · intro a ha g x
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' => exact (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').2.1 g x
    | zero => rfl
    | add a c _ _ ha hc => simp [ha, hc]
    | neg a _ ha => simp [ha]
  · intro H ψ hψ
    change _root_.GlobalTheory.BI.indAddHomComplex H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G
    induction hψ using AddSubgroup.closure_induction with
    | mem ψ hψ' =>
      exact AddSubgroup.subset_closure
        (_root_.GlobalTheory.BI.isChar_ind ℂ ℂ G H ψ hψ')
    | zero => simpa using zero_mem _
    | add ψ φ _ _ hψ hφ => simpa [map_add] using add_mem hψ hφ
    | neg ψ _ hψ => simpa [map_neg] using neg_mem hψ
  · intro lam
    exact _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_monoidHom_complex lam)
end _root_.GlobalTheory.BI
end GlobalTheory.BI
