-- Prove2me | solution 1 for KnodelPrimeCordial.filtered_card_by_product__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:21.909548+00:00
-- url     : https://prove2.me/submissions/5598d4ba-da72-4458-9b4e-90195bf2076a

import Mathlib
theorem KnodelPrimeCordial.filtered_card_by_product__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
    {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (e : Fin m × Fin 3 → α) (s : Finset α) (P : α → Prop)
    [DecidablePred P]
    (he : Set.BijOn e Set.univ (↑s : Set α)) :
    (s.filter P).card =
      ∑ k : Fin 3, (Finset.univ.filter fun j : Fin m => P (e (j, k))).card := by
  classical
  have h1 : (s.filter P).card = (Finset.univ.filter fun x : Fin m × Fin 3 => P (e x)).card := by
    symm
    apply Finset.card_bij (fun x _ => e x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨he.mapsTo (Set.mem_univ x), hx⟩
    · intro a _ b _ hab
      exact he.injOn (Set.mem_univ a) (Set.mem_univ b) hab
    · intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨x, -, rfl⟩ := he.surjOn hy.1
      exact ⟨x, by simp [hy.2], rfl⟩
  rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [Finset.card_filter]

theorem solution
    {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (e : Fin m × Fin 3 → α) (s : Finset α) (P : α → Prop)
    [DecidablePred P]
    (he : Set.BijOn e Set.univ (↑s : Set α)) :
    (s.filter P).card =
      ∑ k : Fin 3, (Finset.univ.filter fun j : Fin m => P (e (j, k))).card := by
  classical
  have h1 : (s.filter P).card = (Finset.univ.filter fun x : Fin m × Fin 3 => P (e x)).card := by
    symm
    apply Finset.card_bij (fun x _ => e x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨he.mapsTo (Set.mem_univ x), hx⟩
    · intro a _ b _ hab
      exact he.injOn (Set.mem_univ a) (Set.mem_univ b) hab
    · intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨x, -, rfl⟩ := he.surjOn hy.1
      exact ⟨x, by simp [hy.2], rfl⟩
  rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [Finset.card_filter]

