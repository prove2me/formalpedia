-- Prove2me | solution 1 for GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:03.678194+00:00
-- url     : https://prove2.me/submissions/5cbfc54c-1af2-4593-84db-77a8f4197812

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Theorems.Thm_GlobalTheory_BI_virt_mul_comap_conj_ind_linear


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G], (∀ a ∈ Virt ℂ ℂ G, ∀ b ∈ Virt ℂ ℂ G, a * b ∈ Virt ℂ ℂ G) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G), (fun h => a (f h)) ∈ Virt ℂ ℂ H) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧ (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ Virt ℂ ℂ H → ind H ψ ∈ Virt ℂ ℂ G) ∧ ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.BI.virt_mul_comap_conj_ind_linear | exact GlobalTheory.BI.virt_mul_comap_conj_ind_linear | (intros; apply GlobalTheory.BI.virt_mul_comap_conj_ind_linear <;> assumption)
end _root_.GlobalTheory.T
