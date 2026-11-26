-- Prove2me | solution 1 for HajnalSzemeredi.CountHyp.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:36.201796+00:00
-- url     : https://prove2.me/submissions/dc970032-bf01-40f8-8ffa-1fd78c26b6e8

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_HajnalSzemeredi_Count
public import Theorems.Thm_HajnalSzemeredi_CountHyp_card_Sy
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
private theorem card_le_nbr_part {v : V} {Q : Finset ℕ} (hQ : Q ⊆ PA)
    (hne : ∀ X ∈ Q, (nIn G S c v X).Nonempty) : Q.card ≤ (nbr G (part S c PA) v).card := by
  rw [card_nbr_part]
  calc Q.card = ∑ X ∈ Q, 1 := by simp
    _ ≤ ∑ X ∈ Q, (nIn G S c v X).card := sum_le_sum fun X hX => (hne X hX).card_pos
    _ ≤ _ := sum_le_sum_of_subset hQ
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
private theorem nIn_eq_filter (y : V) (W : ℕ) :
    nIn G S c y W = (cls S c W).filter fun z => G.Adj y z := by
  ext z
  simp only [nIn, mem_inter, mem_nbr, mem_filter, mem_cls]
  tauto
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
theorem _root_.solution (h : CountHyp G S c PA PB TU r s) {W : ℕ} (hW : W ∈ TU)
    (hW' : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ W → ¬ Movable G S c z X) :
    PB.card + 1 ≤ TU.card ∧ ∀ y ∈ part S c PB, (Sy G S c TU (part S c PB) y).Nonempty := by
  have hq : PB.card + 1 ≤ TU.card := by
    by_contra hlt
    have hz : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).card +
        (nbr G (part S c PB) z).card ≤ 2 * PB.card := by
      intro z hz
      have hzS := (mem_cls.1 hz).1
      have hzc := (mem_cls.1 hz).2
      have h1 := h.card_nbr_split z
      have h3 := h.deg z hzS
      have := h.card_r
      by_cases hne : (Sz G S c TU (part S c PB) z).Nonempty
      · have hA : (PA.erase W).card ≤ (nbr G (part S c PA) z).card := by
          apply card_le_nbr_part (erase_subset _ _)
          intro X hX
          obtain ⟨hXW, hXP⟩ := mem_erase.1 hX
          have hm := hW' z hz hne X hXP hXW
          simp only [Movable, not_forall, not_not] at hm
          obtain ⟨w, hw, hadj⟩ := hm
          exact ⟨w, mem_inter.2 ⟨mem_nbr.2 ⟨(mem_cls.1 hw).1, hadj⟩, hw⟩⟩
        have hsub : Sz G S c TU (part S c PB) z ⊆ nbr G (part S c PB) z := by
          intro y hy
          obtain ⟨hyB, hs⟩ := mem_filter.1 hy
          have : z ∈ nIn G S c y (c z) := by rw [hs.2.2.2]; exact mem_singleton_self z
          exact mem_nbr.2 ⟨hyB, ((mem_nbr.1 (mem_inter.1 this).1).2).symm⟩
        have := card_le_card hsub
        have := card_erase_of_mem (h.sub hW)
        have := card_pos.2 ⟨W, h.sub hW⟩
        omega
      · rw [not_nonempty_iff_eq_empty.1 hne, card_empty]
        have := h.h22 z hzS (hzc ▸ hW)
        omega
    have hupper := sum_le_sum hz
    rw [sum_const, smul_eq_mul, h.size W hW, sum_add_distrib] at hupper
    have hlow : ∑ y ∈ part S c PB, 2 ≤ ∑ y ∈ part S c PB, ((nIn G S c y W).card +
        ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card) :=
      sum_le_sum fun y hy => h.two_le_nIn_add hy hW
    rw [sum_const, smul_eq_mul, h.card_B, sum_add_distrib] at hlow
    have e1 : ∑ z ∈ cls S c W, (nbr G (part S c PB) z).card =
        ∑ y ∈ part S c PB, (nIn G S c y W).card := by
      simp only [nIn_eq_filter, nbr, card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
      simp only [G.adj_comm]
    have e2 : ∑ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).card =
        ∑ y ∈ part S c PB, ((cls S c W).filter fun z => IsSolo G S c TU (part S c PB) z y).card := by
      simp only [Sz, card_filter]
      rw [sum_comm]
    nlinarith
  refine ⟨hq, fun y hy => ?_⟩
  have := h.card_Sy hy
  exact card_pos.1 (by omega)
end HajnalSzemeredi.CountHyp
