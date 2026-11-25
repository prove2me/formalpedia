-- Prove2me | solution 1 for GlobalTheory.exists_algebraicIndependent_ratios_of_generic_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:51.389682+00:00
-- url     : https://prove2.me/submissions/a7252c64-9749-4e7a-8025-ea563ca0919c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero
import Theorems.Thm_GlobalTheory_mem_matroid_closure_of_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ] (m N : ℕ) (t : Fin m × Fin (N + 1) → κ)
    (ζ : Fin (N + 1) → κ) (j0 : Fin (N + 1)), AlgebraicIndependent k t → ζ j0 ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) →
    ∃ J : Fin m → Fin (N + 1), AlgebraicIndependent k (fun a => ζ (J a) / ζ j0) := by
  intro k κ _ _ _ m N t ζ j0 ht h0 hz
  classical
  set M := AlgebraicIndependent.matroid k κ with hM
  set η : Fin (N + 1) → κ := fun j => ζ j / ζ j0 with hη
  set t' : Fin m × Fin N → κ := fun p => t (p.1, j0.succAbove p.2) with ht'
  have hsub : Set.range t ⊆ M.closure (Set.range η ∪ Set.range t') := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply mem_matroid_closure_of_mem_adjoin
    have hmem : ∀ l : Fin N, t (i, j0.succAbove l) ∈
        Algebra.adjoin k (Set.range η ∪ Set.range t') := fun l =>
      Algebra.subset_adjoin (Or.inr ⟨(i, l), rfl⟩)
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨l, rfl⟩
    · have h1 := hz i
      rw [Fin.sum_univ_succAbove _ j] at h1
      have h2 : t (i, j) = -∑ l : Fin N, t (i, j.succAbove l) * η (j.succAbove l) := by
        simp only [hη, ← mul_div_assoc, ← Finset.sum_div]
        field_simp
        linear_combination h1
      rw [h2]
      exact neg_mem (sum_mem fun l _ =>
        mul_mem (hmem l) (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)))
    · exact hmem l
  have hind : M.Indep (Set.range t) := ht.to_subtype_range
  have h1 : M.eRk (Set.range t) = ((m * (N + 1) : ℕ) : ℕ∞) := by
    rw [hind.eRk_eq_encard, ← Set.image_univ, ht.injective.encard_image]
    simp
  have h2 : (Set.range t').encard ≤ ((m * N : ℕ) : ℕ∞) := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  have h3 : ((m * (N + 1) : ℕ) : ℕ∞) ≤ M.eRk (Set.range η) + ((m * N : ℕ) : ℕ∞) := by
    rw [← h1]
    refine (M.eRk_mono hsub).trans ?_
    rw [M.eRk_closure_eq]
    exact (M.eRk_union_le_eRk_add_encard _ _).trans (by gcongr)
  have h4 : (m : ℕ∞) ≤ M.eRk (Set.range η) := by
    have : ((m * (N + 1) : ℕ) : ℕ∞) = (m : ℕ∞) + ((m * N : ℕ) : ℕ∞) := by
      push_cast; ring
    rw [this] at h3
    exact (WithTop.add_le_add_iff_right (ENat.coe_ne_top _)).mp h3
  obtain ⟨I, hIη, hI, hc⟩ := Matroid.le_eRk_iff.mp h4
  have hfin : I.Finite := Set.finite_of_encard_eq_coe hc
  have : Finite I := hfin
  have hcard : Nat.card I = m := by
    rw [Nat.card_coe_set_eq, Set.ncard, hc]; simp
  let e : Fin m ≃ I := (Finite.equivFinOfCardEq hcard).symm
  choose g hg using fun x : I => hIη x.2
  refine ⟨fun a => g (e a), ?_⟩
  have hI' : AlgebraicIndependent k (fun x : I => (x : κ)) := hI
  have := hI'.comp e e.injective
  convert this using 1
  funext a
  exact hg (e a)
end GlobalTheory
