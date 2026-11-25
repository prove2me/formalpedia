-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.exists_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:03.928608+00:00
-- url     : https://prove2.me/submissions/c4304c2f-cb84-45c4-a88d-d3929cc7f122

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_character_eq_sum_irrChars
import Theorems.Thm_GroundTheory_LocalField_exists_nat_charInner_character

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
universe u
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) :
    ∃ m : (G → ℂ) → ℕ, χ = ∑ ψ ∈ irrChars G, (m ψ : ℂ) • ψ := by
  classical
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  have h : ∀ ψ ∈ irrChars G, ∃ m : ℕ, charInner G ρ.character ψ = m := fun ψ hψ ↦
    exists_nat_charInner_character ρ (mem_irrChars.mp hψ)
  choose! m hm using h
  refine ⟨m, ?_⟩
  conv_lhs => rw [character_eq_sum_irrChars ρ]
  exact Finset.sum_congr rfl fun ψ hψ ↦ by rw [hm ψ hψ]
end IsCharacter
end GroundTheory.LocalField
