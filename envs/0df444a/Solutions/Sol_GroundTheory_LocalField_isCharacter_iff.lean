-- Prove2me | solution 1 for GroundTheory.LocalField.isCharacter_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:47.346204+00:00
-- url     : https://prove2.me/submissions/1808cc5d-ab36-4f8f-86d5-fdd119097f35

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_exists_nat_charInner_character
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_nsmul
import Theorems.Thm_GroundTheory_LocalField_isCharacter_sum

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
variable {G : Type*} [Group G]
variable [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution {f : G → ℂ} :
    IsCharacter f ↔ IsClassFun f ∧ ∀ ψ ∈ irrChars G, ∃ n : ℕ, charInner G f ψ = n := by
  classical
  constructor
  · intro hf
    refine ⟨hf.isClassFun, fun ψ hψ ↦ ?_⟩
    obtain ⟨V, _, _, _, ρ, rfl⟩ := hf
    exact exists_nat_charInner_character ρ (mem_irrChars.mp hψ)
  · rintro ⟨hf, h⟩
    choose! n hn using h
    rw [eq_sum_irrChars_of_isClassFun hf]
    refine isCharacter_sum _ fun ψ hψ ↦ ?_
    rw [hn ψ hψ, Nat.cast_smul_eq_nsmul ℂ]
    exact (mem_irrChars.mp hψ).isCharacter.nsmul _
end GroundTheory.LocalField
