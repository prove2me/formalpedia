-- Prove2me | solution 1 for MomentComparison.pair_count_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:04:03.095091+00:00
-- url     : https://prove2.me/submissions/f63835f6-b92a-4c51-90dc-d06fefc17bf0

module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_MomentComparison_Counting

set_option autoImplicit true
@[expose] public section
public section
open scoped symmDiff
open MomentComparison
namespace MomentComparison
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (m k : ℕ) (hkm : k ≤ m) (U : Finset α) (hU : U.card = 2 * k) :
    (2 * k).choose k * (Fintype.card α - 2 * k).choose (m - k) ≤
      (((Finset.univ : Finset α).powersetCard m ×ˢ
        (Finset.univ : Finset α).powersetCard m).filter (fun p => p.1 ∆ p.2 = U)).card := by
  let V := (Finset.univ : Finset α) \ U
  let source := U.powersetCard k ×ˢ V.powersetCard (m - k)
  let extend (p : Finset α × Finset α) :=
    (p.1 ∪ p.2, (U \ p.1) ∪ p.2)
  have size_source : source.card =
      (2 * k).choose k * (Fintype.card α - 2 * k).choose (m - k) := by
    simp [source, V, Finset.card_powersetCard, Finset.card_sdiff_of_subset, hU]
  rw [← size_source]
  refine Finset.card_le_card_of_injOn extend ?_ ?_
  · intro p hp
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp (show p ∈ source from hp)
    obtain ⟨hrSub, hrCard⟩ := Finset.mem_powersetCard.mp hr
    obtain ⟨htSub, htCard⟩ := Finset.mem_powersetCard.mp ht
    have htOutside : Disjoint p.2 U :=
      Finset.disjoint_of_subset_left htSub Finset.sdiff_disjoint
    have hleft : Disjoint p.1 p.2 :=
      Finset.disjoint_of_subset_left hrSub htOutside.symm
    have hright : Disjoint (U \ p.1) p.2 :=
      Finset.disjoint_of_subset_left Finset.sdiff_subset htOutside.symm
    change extend p ∈ Finset.filter _ _
    simp only [extend, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.card_union_of_disjoint hleft, hrCard, htCard, Nat.add_sub_of_le hkm]
    · rw [Finset.card_union_of_disjoint hright, Finset.card_sdiff_of_subset hrSub,
        hU, hrCard, htCard]
      omega
    · ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
      have hrx : x ∈ p.1 → x ∈ U := fun hx => hrSub hx
      have htx : x ∈ p.2 → x ∉ U := fun hx =>
        (Finset.mem_sdiff.mp (htSub hx)).2
      tauto
  · intro p hp q hq heq
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp (show p ∈ source from hp)
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp (show q ∈ source from hq)
    have recover (r t : Finset α) (hr : r ⊆ U) (ht : t ⊆ V) :
        (r ∪ t) ∩ U = r ∧ (r ∪ t) \ U = t := by
      constructor <;> ext x <;> simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      all_goals
        have hrx : x ∈ r → x ∈ U := fun hx => hr hx
        have htx : x ∈ t → x ∉ U := fun hx => (Finset.mem_sdiff.mp (ht hx)).2
        tauto
    obtain ⟨hpLeft, hpRight⟩ := recover p.1 p.2
      (Finset.mem_powersetCard.mp hp₁).1 (Finset.mem_powersetCard.mp hp₂).1
    obtain ⟨hqLeft, hqRight⟩ := recover q.1 q.2
      (Finset.mem_powersetCard.mp hq₁).1 (Finset.mem_powersetCard.mp hq₂).1
    have firstEq : p.1 ∪ p.2 = q.1 ∪ q.2 := congrArg Prod.fst heq
    exact Prod.ext (hpLeft.symm.trans (firstEq ▸ hqLeft))
      (hpRight.symm.trans (firstEq ▸ hqRight))
end MomentComparison
