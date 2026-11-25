-- Prove2me | solution 1 for KneserColouring.kLab_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:37.726111+00:00
-- url     : https://prove2.me/submissions/9e4e4cbe-8693-46ab-bfbb-840293cbedc8

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_maxCol_ne_of_disjoint
public import Theorems.Thm_KneserColouring_posPart_neg
public import Theorems.Thm_KneserColouring_negPart_neg
public import Theorems.Thm_KneserColouring_suppCard_neg
public import Theorems.Thm_KneserColouring_disjoint_posPart_negPart
public import Theorems.Thm_KneserColouring_one_le_maxCol_of_large
public import Theorems.Thm_KneserColouring_signType_neg_ne_self


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {x : Fin n → SignType} (hx : x ≠ 0) : kLab c (-x) = -kLab c x := by
  have hxx : -x ≠ x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    intro h
    have := congrFun h i
    exact signType_neg_ne_self hi this
  unfold kLab
  rw [suppCard_neg, posPart_neg, negPart_neg, neg_neg]
  by_cases hs : suppCard x ≤ 2 * k - 2
  · rw [if_pos hs, if_pos hs]
    by_cases h1 : toLex x < toLex (-x)
    · have h2 : ¬ toLex (-x) < toLex x := lt_asymm h1
      rw [if_pos h1, if_neg h2, neg_neg]
    · have h2 : toLex (-x) < toLex x := by
        rcases lt_trichotomy (toLex (-x)) (toLex x) with h | h | h
        · exact h
        · exact absurd (toLex.injective h) hxx
        · exact absurd h h1
      rw [if_neg h1, if_pos h2]
  · rw [if_neg hs, if_neg hs]
    have hmax := one_le_maxCol_of_large c hk hs
    by_cases h1 : maxCol c (posPart x) < maxCol c (negPart x)
    · have h2 : ¬ maxCol c (negPart x) < maxCol c (posPart x) := by omega
      rw [if_pos h1, if_neg h2, neg_neg]
    · by_cases h2 : maxCol c (negPart x) < maxCol c (posPart x)
      · rw [if_neg h1, if_pos h2]
      · exfalso
        have heq : maxCol c (posPart x) = maxCol c (negPart x) := by omega
        exact maxCol_ne_of_disjoint c hc hk (disjoint_posPart_negPart x)
          (by omega) heq
end KneserColouring
