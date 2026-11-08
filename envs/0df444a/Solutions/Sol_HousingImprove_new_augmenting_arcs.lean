-- Prove2me | solution 1 for HousingImprove.new_augmenting_arcs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:21:22.874389+00:00
-- url     : https://prove2.me/submissions/af7232ce-ca40-4955-ac0c-46ba0c1470ba

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_tildeMarket

universe u

namespace Aux_HInaa

open HousingImprove

variable {N : Type u}

def P (p : N) (H H' : Market N) (a : N) : Prop :=
  (∀ x y, x ≠ p → y ≠ p → (H'.lt a x y ↔ H.lt a x y)) ∧
  (∀ x, H.lt a x p → H'.lt a x p) ∧ (∀ x, H'.lt a p x → H.lt a p x)

theorem P_of_eq (p : N) (H H' : Market N) (a : N) (h : H'.lt a = H.lt a) : P p H H' a := by
  unfold P
  rw [h]
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ h => h, fun _ h => h⟩

theorem P_trans (p : N) (H H₁ H₂ : Market N) (a : N) (h1 : P p H H₁ a) (h2 : P p H₁ H₂ a) :
    P p H H₂ a :=
  ⟨fun x y hx hy => (h2.1 x y hx hy).trans (h1.1 x y hx hy),
    fun x h => h2.2.1 x (h1.2.1 x h), fun x h => h1.2.2 x (h2.2.2 x h)⟩

theorem good (p : N) (qs : List N) :
    ∀ H H' : Market N, ImprovesAlong p qs H H' → H'.lt p = H.lt p ∧ ∀ a, P p H H' a := by
  induction qs with
  | nil =>
    intro H H' h
    simp only [ImprovesAlong] at h
    subst h
    exact ⟨rfl, fun a => P_of_eq p _ _ a rfl⟩
  | cons q qs ih =>
    intro H H' h
    simp only [ImprovesAlong] at h
    obtain ⟨H₁, hi, hr⟩ := h
    obtain ⟨e1, p1⟩ := ih H₁ H' hr
    have hp : H₁.lt p = H.lt p := hi.2.1 p (fun h => hi.1 h.symm)
    have hP : ∀ a, P p H H₁ a := by
      intro a
      by_cases ha : a = q
      · subst ha
        exact ⟨hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
      · exact P_of_eq p H H₁ a (hi.2.1 a ha)
    exact ⟨e1.trans hp, fun a => P_trans p H H₁ H' a (hP a) (p1 a)⟩

end Aux_HInaa

open HousingImprove Aux_HInaa in
theorem solution {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) :
    ∀ a b, H'.lt a (X a) b → ¬ H.lt a (X a) b → a ∈ Q ∧ b = p := by
  intro a b h1 h2
  obtain ⟨qs, hqs⟩ := hH
  obtain ⟨hp, hP⟩ := good p qs H H' hqs
  have hrow : H'.lt a ≠ H.lt a := by
    intro e
    rw [e] at h1
    exact h2 h1
  have hap : a ≠ p := by
    rintro rfl
    exact hrow hp
  obtain ⟨hiff, -, hdown⟩ := hP a
  by_cases hXa : X a = p
  · rw [hXa] at h1 h2
    exact absurd (hdown b h1) h2
  · by_cases hb : b = p
    · rw [hb] at h1 ⊢
      exact ⟨hQ.1 a hap hrow h1, rfl⟩
    · exact absurd ((hiff _ _ hXa hb).mp h1) h2
