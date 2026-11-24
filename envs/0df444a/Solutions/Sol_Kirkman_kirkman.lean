-- Prove2me | solution 1 for Kirkman.kirkman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:40.428826+00:00
-- url     : https://prove2.me/submissions/ef414078-445e-4376-9899-b4622b716ff8

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
public import Theorems.Thm_Kirkman_isSTS_of_equiv
public import Theorems.Thm_Kirkman_two_mul_card_through
public import Theorems.Thm_Kirkman_sum_card_through
public import Theorems.Thm_Kirkman_boseQ_idem


set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
namespace Kirkman
theorem _root_.solution (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 := by
  constructor
  · rintro ⟨𝒯, h𝒯⟩
    set d := #(𝒯.filter (fun T => (⟨0, hv⟩ : Fin v) ∈ T))
    have hd : 2 * d = v - 1 := two_mul_card_through h𝒯 _
    have hsum := sum_card_through h𝒯
    have hall : ∀ x : Fin v, #(𝒯.filter (fun T => x ∈ T)) = d := by
      intro x
      have := two_mul_card_through h𝒯 x
      omega
    rw [sum_congr rfl (fun x _ => hall x), sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at hsum
    have h3 : 3 ∣ v * d := ⟨#𝒯, hsum⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with ⟨a, ha⟩ | ⟨c, hc⟩ <;> omega
  · rintro (h | h)
    · by_cases hv1 : v = 1
      · subst hv1
        refine ⟨∅, fun T hT => absurd hT (notMem_empty _), fun x y hxy => ?_⟩
        exact absurd (Subsingleton.elim x y) hxy
      · obtain ⟨t, rfl⟩ : ∃ t, v = 6 * t + 7 := ⟨(v - 7) / 6, by omega⟩
        exact isSTS_of_equiv (skolemSteiner (skolemQ t)) (by simp; ring)
    · obtain ⟨n, rfl⟩ : ∃ n, v = 3 * n := ⟨v / 3, by omega⟩
      have hn : n % 2 = 1 := by omega
      have : NeZero n := ⟨by omega⟩
      exact isSTS_of_equiv (boseSteiner (boseQ hn) (boseQ_idem hn)) (by simp; ring)
end Kirkman
