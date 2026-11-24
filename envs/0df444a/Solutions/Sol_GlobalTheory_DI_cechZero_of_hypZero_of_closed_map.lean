-- Prove2me | solution 1 for GlobalTheory.DI.cechZero_of_hypZero_of_closed_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:22.127804+00:00
-- url     : https://prove2.me/submissions/8719671c-398b-4f67-8c11-558693746c14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_TotalDifferentialCupProduct
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CechVanishingAlongFiltration
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CupProductFiltrationBound
import Theorems.Thm_GlobalTheory_DI_Dtot_cup
import Theorems.Thm_GlobalTheory_DI_cechZero_of_hypZero_filtered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
private theorem card_filter_le_add_card_filter_ge {ι : Type} [LinearOrder ι] (u : Finset ι) (j : ι)
    (hj : j ∈ u) : ({x ∈ u | x ≤ j}).card + ({x ∈ u | j ≤ x}).card = u.card + 1 := by
  have hU : ({x ∈ u | x ≤ j}) ∪ ({x ∈ u | j ≤ x}) = u := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      rcases le_total x j with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hI : ({x ∈ u | x ≤ j}) ∩ ({x ∈ u | j ≤ x}) = {j} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h1 h2
    · rintro rfl
      exact ⟨⟨hj, le_refl _⟩, ⟨hj, le_refl _⟩⟩
  have h := Finset.card_union_add_card_inter ({x ∈ u | x ≤ j}) ({x ∈ u | j ≤ x})
  rw [hU, hI, Finset.card_singleton] at h
  omega
end GlobalTheory.DI
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro ι _ E _ d N T Φ hdd hN hT hd hΦ0 hΦD hΦT hC a b hH
  let Ψ : (Finset ι → E) →+ (Finset ι → E) := AddMonoidHom.mk' (fun c => cup Φ c) (by
    intro c c'
    funext u
    simp only [cup, Pi.add_apply, map_add, Finset.sum_add_distrib])
  have hΨ : ∀ c, Ψ c = cup Φ c := fun c => rfl
  let γ : Finset ι → E → E := fun s x => if h : s.Nonempty then Φ x {s.max' h} else 0
  refine cechZero_of_hypZero_filtered d N T Ψ γ hdd hN hT hd ?_ ?_ ?_ ?_ a b hH
  · intro m c hc
    rw [hΨ, hΨ]
    exact Dtot_cup d Φ c hΦ0 hc.1 (fun s => hΦD _)
  · intro m c hc
    rw [hΨ]
    refine ⟨?_, fun q u hq => ?_, fun u hu => ?_⟩
    · simp [cup]
    · simp only [cup]
      refine sum_mem fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).1 q (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
        exact zero_mem _
    · simp only [cup]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).2 (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
  · intro s hs
    have hγs : γ s = fun x => Φ x {s.max' hs} := by
      funext x
      simp only [γ, dif_pos hs]
    rw [hγs]
    exact hC s (s.max' hs) (s.max'_mem hs)
  · intro m c u hc hu hlow
    rw [hΨ]
    simp only [cup]
    rw [Finset.sum_eq_single_of_mem (u.max' hu) (u.max'_mem hu)]
    · have hL : ({x ∈ u | x ≤ u.max' hu}) = u := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.1
        · intro hx
          exact ⟨hx, u.le_max' x hx⟩
      have hR : ({x ∈ u | u.max' hu ≤ x}) = {u.max' hu} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hle⟩
          exact le_antisymm (u.le_max' x hx) hle
        · rintro rfl
          exact ⟨u.max'_mem hu, le_refl _⟩
      rw [hL, hR]
      simp only [γ, dif_pos hu]
    · intro j hj hne
      have hlt : ({x ∈ u | x ≤ j}).card < u.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
        have hm := hsub (u.max'_mem hu)
        simp only [Finset.mem_filter] at hm
        exact hne (le_antisymm (u.le_max' j hj) hm.2)
      rw [hlow _ hlt, map_zero, Pi.zero_apply]
end GlobalTheory.DI
