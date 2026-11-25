-- Prove2me | solution 1 for GlobalTheory.BI.irrChar_linear_or_induced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:52.622409+00:00
-- url     : https://prove2.me/submissions/572f09d2-abb4-4a5f-9292-c76baeefbdf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Theorems.Thm_GlobalTheory_BI_nontrivial_of_isIrreducible
import Theorems.Thm_GlobalTheory_T_character_eq_induced_of_imprimitivity_system
import Theorems.Thm_GlobalTheory_T_commute_image_abelianByPrimePower_of_normal_central
import Theorems.Thm_GlobalTheory_T_exists_character_eigenvector_of_commuting_representation
import Theorems.Thm_GlobalTheory_T_exists_weight_idempotent_of_eigenvector
import Theorems.Thm_GlobalTheory_T_idempotent_eq_one_and_character_eq_of_isIrreducible


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
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  intro L _ _ _ G _ _ χ hG ⟨n, ρ, hρ, hχ⟩
  have hχ' : ∀ g, χ g = ρ.character g := fun g => by simpa using hχ g
  haveI := nontrivial_of_isIrreducible ρ hρ
  by_cases hR : ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ
  · exact Or.inr hR
  left
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible L G (Fin n → L) ρ hρ
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    refine GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central G (Module.End L (Fin n → L)) ρ hG ?_
    intro B hB hBc
    obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L B (Fin n → L) (ρ.comp B.subtype)
      (fun a b => hBc a a.2 b b.2)
    obtain ⟨e, he0, hee, heB, heT, heN⟩ := GlobalTheory.T.exists_weight_idempotent_of_eigenvector L G (Fin n → L) ρ B
      (weightStabiliser B hB lam) lam v hB hv hlam (fun _ => Iff.rfl)
    obtain ⟨ψ, hψ, hind⟩ := GlobalTheory.T.character_eq_induced_of_imprimitivity_system L G (Fin n → L) ρ _ e hρ he0 hee heT heN
    have hT : weightStabiliser B hB lam = ⊤ := by
      by_contra hT
      exact hR ⟨_, hT, ψ, hψ, funext fun g => (hχ' g).trans (hind g)⟩
    have he1 : e = 1 := hs1 e he0 hee (fun g => heT g (hT ▸ Subgroup.mem_top g))
    intro b hb g
    have := heB ⟨b, hb⟩
    rw [he1, mul_one] at this
    change ρ b = _ at this
    rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L G (Fin n → L) ρ hcomm
  exact ⟨lam, fun g => (hχ' g).trans (hs2 lam v hv hlam g)⟩
end GlobalTheory.BI
