-- Prove2me | solution 1 for HajnalSzemeredi.CountHyp.card_Sy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:08.413813+00:00
-- url     : https://prove2.me/submissions/2c8803f0-cec8-4862-99f8-d23adcb5ffdf

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_HajnalSzemeredi_Count
public import Theorems.Thm_HajnalSzemeredi_cls_disjoint
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr


section
@[expose] public section
noncomputable section
open Classical Finset
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace CountHyp
variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}
private theorem mem_part' {Q : Finset ℕ} {v : V} : v ∈ part S c Q ↔ v ∈ S ∧ c v ∈ Q := by
  simp [part]
private theorem card_nbr_split (h : CountHyp G S c PA PB TU r s) (v : V) :
    (nbr G S v).card = (nbr G (part S c PA) v).card + (nbr G (part S c PB) v).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext w
    simp only [mem_union, mem_nbr, mem_part']
    constructor
    · rintro ⟨hw, ha⟩
      rcases mem_union.1 (h.cover w hw) with h1 | h1
      · exact Or.inl ⟨⟨hw, h1⟩, ha⟩
      · exact Or.inr ⟨⟨hw, h1⟩, ha⟩
    · rintro (⟨⟨hw, _⟩, ha⟩ | ⟨⟨hw, _⟩, ha⟩) <;> exact ⟨hw, ha⟩
  · rw [disjoint_left]
    intro w h1 h2
    simp only [mem_nbr, mem_part'] at h1 h2
    exact disjoint_left.1 h.disj h1.1.2 h2.1.2
private theorem card_nbr_part (v : V) (Q : Finset ℕ) :
    (nbr G (part S c Q) v).card = ∑ X ∈ Q, (nIn G S c v X).card := by
  rw [← card_biUnion]
  · congr 1
    ext w
    simp only [mem_nbr, mem_part', mem_biUnion, nIn, mem_inter, mem_cls]
    constructor
    · rintro ⟨⟨hw, hc⟩, ha⟩
      exact ⟨c w, hc, ⟨hw, ha⟩, hw, rfl⟩
    · rintro ⟨X, hX, ⟨hw, ha⟩, _, rfl⟩
      exact ⟨⟨hw, hX⟩, ha⟩
  · intro i _ j _ hij
    exact (cls_disjoint hij).mono inter_subset_right inter_subset_right
private theorem two_le_nIn_add (h : CountHyp G S c PA PB TU r s) {y : V}
    (hy : y ∈ part S c PB) {W : ℕ} (hW : W ∈ TU) :
    2 ≤ (nIn G S c y W).card +
      ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
  have hpos := (h.h21 y hy W (h.sub hW)).card_pos
  by_cases h2 : 2 ≤ (nIn G S c y W).card
  · omega
  · have h1 : (nIn G S c y W).card = 1 := by omega
    obtain ⟨a, ha⟩ := card_eq_one.1 h1
    have haW : a ∈ cls S c W := by
      have : a ∈ nIn G S c y W := by rw [ha]; exact mem_singleton_self a
      exact (mem_inter.1 this).2
    rw [mem_cls] at haW
    have : 0 < ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
      refine card_pos.2 ⟨a, mem_filter.2 ⟨mem_cls.2 haW, haW.1, haW.2 ▸ hW, hy, ?_⟩⟩
      rw [haW.2]; exact ha
    omega
end CountHyp
end HajnalSzemeredi
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
open HajnalSzemeredi.CountHyp
variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}
namespace HajnalSzemeredi.CountHyp
theorem _root_.solution (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    TU.card + 1 + (nbr G (part S c PB) y).card ≤
      (Sy G S c TU (part S c PB) y).card + PB.card := by
  have hsum : ∑ X ∈ TU, ((cls S c X).filter fun z => IsSolo G S c TU (part S c PB) z y).card ≤
      (Sy G S c TU (part S c PB) y).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro z hz
      simp only [mem_biUnion, mem_filter, mem_cls] at hz
      obtain ⟨X, _, ⟨hzS, _⟩, hs⟩ := hz
      exact mem_filter.2 ⟨hzS, hs⟩
    · intro i _ j _ hij
      exact (cls_disjoint hij).mono (filter_subset _ _) (filter_subset _ _)
  have hTU : ∑ X ∈ TU, 2 ≤ ∑ X ∈ TU, ((nIn G S c y X).card +
      ((cls S c X).filter fun z => IsSolo G S c TU (part S c PB) z y).card) :=
    sum_le_sum fun X hX => h.two_le_nIn_add hy hX
  rw [sum_add_distrib, sum_const, smul_eq_mul] at hTU
  have hrest : (PA \ TU).card ≤ ∑ X ∈ PA \ TU, (nIn G S c y X).card := by
    calc (PA \ TU).card = ∑ X ∈ PA \ TU, 1 := by simp
      _ ≤ _ := sum_le_sum fun X hX => (h.h21 y hy X (mem_sdiff.1 hX).1).card_pos
  have hA := card_nbr_part (G := G) (S := S) (c := c) y PA
  rw [← sum_sdiff h.sub] at hA
  have hc := card_sdiff_add_card_eq_card h.sub
  have h1 := h.card_nbr_split y
  have h3 := h.deg y (mem_part'.1 hy).1
  have := h.card_r
  omega
end HajnalSzemeredi.CountHyp
