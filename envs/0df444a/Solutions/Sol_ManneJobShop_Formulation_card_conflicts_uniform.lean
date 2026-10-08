-- Prove2me | solution 1 for ManneJobShop.Formulation.card_conflicts_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:18:01.782981+00:00
-- url     : https://prove2.me/submissions/50d45673-88bd-41a7-b682-51460a50c4e7

import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model



namespace ManneJobShop.Formulation

theorem pairs_card {α : Type*} [LinearOrder α] (S : Finset α) :
    2 * ((S ×ˢ S).filter (fun q : α × α => q.1 < q.2)).card + S.card = S.card * S.card := by
  have h1 : (S ×ˢ S).card = ((S ×ˢ S).filter (fun q : α × α => q.1 < q.2)).card
      + ((S ×ˢ S).filter (fun q : α × α => ¬ q.1 < q.2)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have h2 : ((S ×ˢ S).filter (fun q : α × α => ¬ q.1 < q.2)).card
      = ((S ×ˢ S).filter (fun q : α × α => q.2 < q.1)).card
        + ((S ×ˢ S).filter (fun q : α × α => q.1 = q.2)).card := by
    have : ((S ×ˢ S).filter (fun q : α × α => ¬ q.1 < q.2))
        = ((S ×ˢ S).filter (fun q : α × α => q.2 < q.1)) ∪ ((S ×ˢ S).filter (fun q : α × α => q.1 = q.2)) := by
      ext q; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_or_eq_of_le (not_lt.mp h') with h'' | h''
        · exact Or.inl ⟨h, h''⟩
        · exact Or.inr ⟨h, h''.symm⟩
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, not_lt.mpr h'.le⟩
        · exact ⟨h, by rw [h']; exact lt_irrefl _⟩
    rw [this, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_filter]
    intro q _ h1 h2; rw [h2] at h1; exact lt_irrefl _ h1
  have h3 : ((S ×ˢ S).filter (fun q : α × α => q.2 < q.1)).card
      = ((S ×ˢ S).filter (fun q : α × α => q.1 < q.2)).card := by
    apply Finset.card_bij (fun q _ => (q.2, q.1))
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢; tauto
    · intro a _ b _ h; simpa [Prod.ext_iff, and_comm] using h
    · intro q hq; refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢; tauto
  have h4 : ((S ×ˢ S).filter (fun q : α × α => q.1 = q.2)).card = S.card := by
    apply Finset.card_bij (fun q _ => q.1)
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_product] at hq; exact hq.1.1
    · intro a ha b hb h
      simp only [Finset.mem_filter, Finset.mem_product] at ha hb
      exact Prod.ext h (ha.2.symm.trans (h.trans hb.2))
    · intro s hs; exact ⟨(s, s), by simp [hs], rfl⟩
  rw [Finset.card_product] at h1
  omega

theorem cc_core {n : ℕ} (I : Instance n) (p : ℕ)
    (hp : ∀ i : Fin I.M, (Finset.univ.filter (fun j : Fin n => I.mach j = i)).card = p) :
    n = I.M * p ∧ (conflicts I).card = I.M * (p * (p - 1) / 2) := by
  constructor
  · have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin I.M))) (f := I.mach) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simpa [hp] using this
  · have := Finset.card_eq_sum_card_fiberwise (s := conflicts I)
      (t := (Finset.univ : Finset (Fin I.M))) (f := fun q => I.mach q.1) (fun _ _ => Finset.mem_univ _)
    rw [this]
    have hfib : ∀ i : Fin I.M, ((conflicts I).filter (fun q => I.mach q.1 = i)).card = p * (p - 1) / 2 := by
      intro i
      set S := Finset.univ.filter (fun j : Fin n => I.mach j = i) with hS
      have hEq : (conflicts I).filter (fun q => I.mach q.1 = i)
          = (S ×ˢ S).filter (fun q : Fin n × Fin n => q.1 < q.2) := by
        ext q
        simp only [conflicts, hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h2 ▸ h3⟩, h1⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1.trans h2.symm⟩, h1⟩
      rw [hEq]
      have := pairs_card S
      rw [hp i] at this
      have he : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
      have h6 := Nat.mul_div_cancel' he
      have h7 : p * p = p * (p - 1) + p := by
        rcases p with _ | p
        · simp
        · simp [Nat.mul_succ]
      omega
    simp [hfib]

end ManneJobShop.Formulation

open ManneJobShop.Formulation


theorem solution {n : ℕ} (I : Instance n) (p : ℕ)
    (hp : ∀ i : Fin I.M, (Finset.univ.filter (fun j : Fin n => I.mach j = i)).card = p) :
    n = I.M * p ∧ (conflicts I).card = I.M * (p * (p - 1) / 2) := by
  exact cc_core I p hp
