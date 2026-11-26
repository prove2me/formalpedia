-- Prove2me | solution 1 for HajnalSzemeredi.CountHyp.deg_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:09.1585+00:00
-- url     : https://prove2.me/submissions/6e884ccf-84f9-4b27-a075-1fce4855f59b

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
private theorem card_le_nbr_part {v : V} {Q : Finset ℕ} (hQ : Q ⊆ PA)
    (hne : ∀ X ∈ Q, (nIn G S c v X).Nonempty) : Q.card ≤ (nbr G (part S c PA) v).card := by
  rw [card_nbr_part]
  calc Q.card = ∑ X ∈ Q, 1 := by simp
    _ ≤ ∑ X ∈ Q, (nIn G S c v X).card := sum_le_sum fun X hX => (hne X hX).card_pos
    _ ≤ _ := sum_le_sum_of_subset hQ
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
    (nbr G (part S c PB) y).card + 1 ≤ PB.card := by
  have h1 := h.card_nbr_split y
  have h2 := card_le_nbr_part (G := G) (S := S) (c := c) (v := y) (subset_refl PA) (h.h21 y hy)
  have h3 := h.deg y (mem_part'.1 hy).1
  have := h.card_r
  omega
end HajnalSzemeredi.CountHyp
