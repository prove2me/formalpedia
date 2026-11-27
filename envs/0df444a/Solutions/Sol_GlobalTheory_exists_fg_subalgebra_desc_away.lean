-- Prove2me | solution 1 for GlobalTheory.exists_fg_subalgebra_desc_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:36.955432+00:00
-- url     : https://prove2.me/submissions/033cf1ce-b8fd-4850-92e7-c11fcdf6505e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFgSubalgebraDescAway
import Theorems.Thm_GlobalTheory_exists_awayMap_subalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S] (S₀ : Subalgebra K S), S₀.FG → ∀ (n : ℕ) (h : Fin n → S) (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)], (∀ i, Algebra.FiniteType K (A i)) → ∀ a : ∀ i, A i →ₐ[K] Localization.Away (h i), Ideal.span (Set.range h) = ⊤ → ∃ (S₁ : Subalgebra K S) (h₁ : Fin n → S₁), S₁.FG ∧ S₀ ≤ S₁ ∧ (∀ i, (h₁ i : S) = h i) ∧ Ideal.span (Set.range h₁) = ⊤ ∧ ∀ i, ∃ (κ : Localization.Away (h₁ i) →ₐ[K] Localization.Away (h i)) (a' : A i →ₐ[K] Localization.Away (h₁ i)), (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧ κ.comp a' = a i := by
  classical
  intro K _ S _ _ S₀ hS₀ n h A _ _ hA a hspan
  obtain ⟨c, hc⟩ : ∃ c : Fin n → S, ∑ i, c i * h i = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hspan ▸ Submodule.mem_top)
  choose G hG using fun i => (hA i).out
  choose m s hs using fun i (g : A i) => IsLocalization.Away.surj (h i) (a i g)
  let T : Finset S := Finset.univ.image h ∪ Finset.univ.image c ∪
    Finset.univ.biUnion fun i => (G i).image (s i)
  let S₁ : Subalgebra K S := S₀ ⊔ Algebra.adjoin K (T : Set S)
  have hT : ∀ t ∈ T, t ∈ S₁ := fun t ht =>
    (le_sup_right : Algebra.adjoin K (T : Set S) ≤ S₁) (Algebra.subset_adjoin ht)
  have hh : ∀ i, h i ∈ S₁ := fun i => hT _ (by simp [T])
  have hcm : ∀ i, c i ∈ S₁ := fun i => hT _ (by simp [T])
  have hsm : ∀ i, ∀ g ∈ G i, s i g ∈ S₁ := fun i g hg => hT _ (by
    simp only [T, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    exact Or.inr ⟨i, Finset.mem_univ _, g, hg, rfl⟩)
  refine ⟨S₁, fun i => ⟨h i, hh i⟩, hS₀.sup ⟨T, rfl⟩, le_sup_left, fun _ => rfl, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨c i, hcm i⟩, Subtype.ext ?_⟩
    simpa using hc
  · intro i
    obtain ⟨κ, hκ, hinj, hr⟩ := exists_awayMap_subalgebra K S S₁ (h i) (hh i)
    have hmem : ∀ y : A i, a i y ∈ κ.range := by
      intro y
      have : (⊤ : Subalgebra K (A i)) ≤ κ.range.comap (a i) := by
        rw [← hG i, Algebra.adjoin_le_iff]
        intro g hg
        exact hr _ (m i g) _ (hsm i g hg) (hs i g)
      exact this Algebra.mem_top
    refine ⟨κ, (AlgEquiv.ofInjective κ hinj).symm.toAlgHom.comp ((a i).codRestrict _ hmem),
      hκ, hinj, ?_⟩
    ext y
    have := AlgEquiv.ofInjective_apply κ hinj
      ((AlgEquiv.ofInjective κ hinj).symm ⟨a i y, hmem y⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
end GlobalTheory
