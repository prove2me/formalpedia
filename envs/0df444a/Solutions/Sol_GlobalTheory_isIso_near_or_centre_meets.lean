-- Prove2me | solution 1 for GlobalTheory.isIso_near_or_centre_meets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:39.335694+00:00
-- url     : https://prove2.me/submissions/3dead605-67cd-4627-a4b4-b4f11ee80354

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoNearOrCentreMeets
import Theorems.Thm_GlobalTheory_SeqFirst_isIso_restrict_of_le
import Theorems.Thm_GlobalTheory_SeqFirst_exists_preimage
import Theorems.Thm_GlobalTheory_SeqFirst_injOn
import Theorems.Thm_GlobalTheory_SeqFirst_isOpen_image
import Theorems.Thm_GlobalTheory_Principalise_isIso_restrict_of_blowup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.SeqFirst
namespace GlobalTheory
theorem _root_.solution : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  intro S Y f B y Y' s h
  induction h with
  | id => exact Or.inl ⟨⊤, trivial, inferInstance⟩
  | @step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih =>
    rcases ih with ⟨U, hyU, hU⟩ | hr
    · obtain ⟨y', hy'U, hy'⟩ := exists_preimage s hyU
      by_cases hJ : y' ∈ J.support
      · exact Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩
      · left
        have hA : IsOpen ((J.support : Set Y₁)ᶜ) := J.support.isClosed.isOpen_compl
        let V : Y.Opens := ⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩
        have hVU : V ≤ U := by
          rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
        have hyV : y ∈ V := ⟨y', ⟨hJ, hy'U⟩, hy'⟩
        refine ⟨V, hyV, ?_⟩
        have : IsIso (s ∣_ V) := isIso_restrict_of_le s hVU
        have hπ : IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
          refine Principalise.isIso_restrict_of_blowup h₃ _ ?_
          intro x hx hxJ
          have hxU : x ∈ s ⁻¹ᵁ U := hVU hx
          obtain ⟨w, ⟨hwA, hwU⟩, hw⟩ := (hx : s x ∈ V)
          exact hwA (injOn s hwU hxU hw ▸ hxJ)
        rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' hπ this
    · right; exact hr
end GlobalTheory
