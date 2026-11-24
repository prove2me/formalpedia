-- Prove2me | solution 1 for GlobalTheory.universallyClosed_of_jointly_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:20.578472+00:00
-- url     : https://prove2.me/submissions/cb3ce117-92ed-4664-beac-91b2d3e78bb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))
end GlobalTheory
