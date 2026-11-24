-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:08.391914+00:00
-- url     : https://prove2.me/submissions/b1087084-fd20-4abd-977b-86fddba9a5b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
import Theorems.Thm_GlobalTheory_BaireDistribution_indicator_mem
import Theorems.Thm_GlobalTheory_BaireDistribution_isCompact_support
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {X : Type} [TopologicalSpace X]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution (D : SB X →ₗ[ℂ] ℂ) (𝒞 : Set X → Prop) (hcl : ∀ C, 𝒞 C → IsClopen C) (h0 : 𝒞 ∅)
    (hu : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∪ C')) (hi : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∩ C'))
    (hd : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C \ C')) (φ : SB X)
    (h : ∀ x ∈ Function.support φ.1, ∃ C, 𝒞 C ∧ x ∈ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) : D φ = 0 := by
  have key : ∃ C, 𝒞 C ∧ Function.support φ.1 ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0 := by
    refine (isCompact_support φ).induction_on (p := fun s => ∃ C, 𝒞 C ∧ s ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, h0, subset_rfl, fun C' _ hC' ψ hψ => ?_⟩
      have : ψ = 0 := Subtype.ext (by rw [hψ, Set.subset_empty_iff.1 hC']; ext; simp)
      rw [this, map_zero]
    · rintro s t hst ⟨C, h1, h2, h3⟩
      exact ⟨C, h1, hst.trans h2, h3⟩
    · rintro s t ⟨C, h1, h2, h3⟩ ⟨E, e1, e2, e3⟩
      refine ⟨C ∪ E, hu _ _ h1 e1, Set.union_subset_union h2 e2, fun C' hC' hs ψ hψ => ?_⟩
      have a1 := h3 (C' ∩ C) (hi _ _ hC' h1) Set.inter_subset_right
        ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ rfl
      have a2 := e3 (C' \ C) (hd _ _ hC' h1) (fun x hx => (hs hx.1).resolve_left hx.2)
        ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ rfl
      have : ψ = ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ +
          ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ := by
        apply Subtype.ext
        rw [hψ]
        ext x
        by_cases a : x ∈ C' <;> by_cases b : x ∈ C <;> simp [Set.indicator, a, b]
      rw [this, map_add, a1, a2, add_zero]
    · intro x hx
      obtain ⟨C, h1, h2, h3⟩ := h x hx
      exact ⟨C, mem_nhdsWithin_of_mem_nhds ((hcl _ h1).2.mem_nhds h2), C, h1, subset_rfl, h3⟩
  obtain ⟨C, h1, h2, h3⟩ := key
  exact h3 C h1 subset_rfl φ (Set.indicator_eq_self.2 h2).symm
end GlobalTheory.BaireDistribution
