-- Prove2me | solution 1 for GlobalTheory.BI.exists_irrChar_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:57.607463+00:00
-- url     : https://prove2.me/submissions/405227f8-b224-4fd6-a964-727a3a6d2fa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAdd
import Theorems.Thm_GlobalTheory_BI_exists_irreducible_subrepresentation
import Theorems.Thm_GlobalTheory_T_exists_character_quotient_of_injective_intertwining
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_of_representation


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl
end GlobalTheory.BI
