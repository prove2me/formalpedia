-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.exists_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:54.333341+00:00
-- url     : https://prove2.me/submissions/7c1c19bf-fce2-453e-81ce-2f68d9915dac

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

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
omit [Fintype G]
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {χ : G → ℂ} (h : IsIrrCharacter χ) : ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := h
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  exact ⟨finrank ℂ V, finrank_pos, char_one ρ⟩
end IsIrrCharacter
end GroundTheory.LocalField
