-- Prove2me | solution 1 for HallReps.CDR.theorem1_hall
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:49.800591+00:00
-- url     : https://prove2.me/submissions/0b4a6b15-46a6-4851-bf1f-8d3bea63b113

import Mathlib
import Definitions.Def_HallReps_CDR_System

set_option autoImplicit false

open HallReps.CDR

namespace HallPk

/-- Hall's theorem for finite index sets and arbitrary (possibly infinite) sets. -/
theorem pk_hall {ι α : Type*} [Finite ι] (T : ι → Set α) (h : HallCondition T) :
    ∃ a : ι → α, IsCDR T a := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- for every subset `s` of indices choose a finite set `F s ⊆ ⋃_{i ∈ s} T i` with `|s|` elements
  have hex : ∀ s : Finset ι, ∃ F : Finset α, (F : Set α) ⊆ ⋃ i ∈ s, T i ∧ s.card ≤ F.card := by
    intro s
    have hs := h s
    by_cases hfin : (⋃ i ∈ s, T i).Finite
    · refine ⟨hfin.toFinset, by simp, ?_⟩
      have h1 : (⋃ i ∈ s, T i).encard = (hfin.toFinset.card : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, hfin.coe_toFinset]
      rw [h1] at hs
      exact_mod_cast hs
    · -- an infinite set contains finite subsets of every size
      obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin s.card
      exact ⟨F, hF, hcard.ge⟩
  choose F hFsub hFcard using hex
  let G : Finset α := Finset.univ.biUnion F
  let t : ι → Finset α := fun i => G.filter (fun x => x ∈ T i)
  have hHall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    refine (hFcard s).trans (Finset.card_le_card ?_)
    intro x hx
    have hxT : x ∈ ⋃ i ∈ s, T i := hFsub s hx
    simp only [Set.mem_iUnion] at hxT
    obtain ⟨i, hi, hxi⟩ := hxT
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hx⟩, hxi⟩
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  exact ⟨f, hf, fun i => (Finset.mem_filter.mp (hmem i)).2⟩

end HallPk

theorem solution {ι α : Type*} [Finite ι] (T : ι → Set α) (h : HallCondition T) :
    ∃ a : ι → α, IsCDR T a := HallPk.pk_hall T h

#print axioms solution
