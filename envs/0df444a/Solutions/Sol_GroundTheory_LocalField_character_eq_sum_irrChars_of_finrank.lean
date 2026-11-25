-- Prove2me | solution 1 for GroundTheory.LocalField.character_eq_sum_irrChars_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:31:07.783716+00:00
-- url     : https://prove2.me/submissions/f88b652a-3f30-490a-8d60-7d9b678379b7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_character
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
universe u
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
      finrank ℂ V = n → ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn
  by_cases hirr : ρ.IsIrreducible
  · rw [Finset.sum_eq_single ρ.character]
    · rw [charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (isIrrCharacter_character ρ),
        if_pos rfl, one_smul]
    · intro ψ hψ hne
      rw [charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (mem_irrChars.mp hψ),
        if_neg (Ne.symm hne), zero_smul]
    · intro h
      exact absurd (mem_irrChars.mpr (isIrrCharacter_character ρ)) h
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : ρ.character = 0 := funext fun g ↦ by
      have : ρ g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
      simp [Representation.character, this]
    rw [h0]
    simp
  have hnt : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩
  obtain ⟨U, hU⟩ : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hirr { toNontrivial := hnt, eq_bot_or_eq_top := fun U ↦ or_iff_not_imp_left.mpr (h U) }
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨U', hUU'⟩ := exists_isCompl U
  have hc : IsCompl U.toSubmodule U'.toSubmodule :=
    ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
      codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
  have hsplit : ρ.character = U.toRepresentation.character + U'.toRepresentation.character := by
    funext g
    let e := Submodule.prodEquivOfIsCompl _ _ hc
    have : ρ g = e.conj ((U.toRepresentation g).prodMap (U'.toRepresentation g)) := by
      apply LinearMap.ext
      intro v
      obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
      simp [LinearEquiv.conj_apply, e, Subrepresentation.toRepresentation,
        Submodule.coe_prodEquivOfIsCompl']
    simp only [Representation.character, Pi.add_apply, this, LinearMap.trace_conj',
      LinearMap.trace_prodMap']
  have hlt : ∀ U'' : Subrepresentation ρ, U'' ≠ ⊤ → finrank ℂ U''.toSubmodule < n := fun U'' h ↦
    hn ▸ Submodule.finrank_lt fun h' ↦ h (Subrepresentation.toSubmodule_injective h')
  have hU'top : U' ≠ ⊤ := by
    intro h
    apply hU.1
    rw [h] at hUU'
    simpa using hUU'.inf_eq_bot
  have h1 := ih _ (hlt U hU.2) _ U.toRepresentation rfl
  have h2 := ih _ (hlt U' hU'top) _ U'.toRepresentation rfl
  rw [hsplit]
  conv_lhs => rw [h1, h2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ψ _ ↦ ?_
  rw [map_add, LinearMap.add_apply, add_smul]
end GroundTheory.LocalField
