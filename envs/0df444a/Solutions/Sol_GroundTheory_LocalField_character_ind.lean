-- Prove2me | solution 1 for GroundTheory.LocalField.character_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:58.394101+00:00
-- url     : https://prove2.me/submissions/72c33c36-b793-433a-ad40-2a3e44ad8a90

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_charInner_character_character
import Theorems.Thm_GroundTheory_LocalField_charInner_comm
import Theorems.Thm_GroundTheory_LocalField_eq_of_isClassFun_of_charInner
import Theorems.Thm_GroundTheory_LocalField_isCharacter_character
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G H : Type*} [Group G] [Group H] (φ : H →* G)
  {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (ρ : Representation ℂ H A) (σ : Representation ℂ G B)
variable [Fintype G] [Fintype H] [FiniteDimensional ℂ A]
namespace GroundTheory.LocalField
theorem _root_.solution : (ind φ ρ).character = indFun φ ρ.character := by
  apply eq_of_isClassFun_of_charInner (isCharacter_character _).isClassFun (isClassFun_indFun _ _)
  intro χ hχ
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := mem_irrChars.mp hχ
  rw [charInner_indFun _ _ (isCharacter_character σ).isClassFun, charInner_comm,
    charInner_character_character, charInner_comm,
    show σ.character ∘ φ = Representation.character (σ.comp φ) from rfl, charInner_character_character,
    (indResEquiv φ ρ σ).finrank_eq]
end GroundTheory.LocalField
