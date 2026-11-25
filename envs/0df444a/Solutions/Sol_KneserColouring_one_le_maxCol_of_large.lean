-- Prove2me | solution 1 for KneserColouring.one_le_maxCol_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:34.745996+00:00
-- url     : https://prove2.me/submissions/1c60f652-e917-42d9-b1eb-37daeb5fd8a1

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_one_le_maxCol
public import Theorems.Thm_KneserColouring_card_posPart_add_negPart

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) (hk : 0 < k)
    {x : Fin n → SignType} (hx : ¬ suppCard x ≤ 2 * k - 2) :
    1 ≤ maxCol c (posPart x) ∨ 1 ≤ maxCol c (negPart x) := by
  have := card_posPart_add_negPart x
  by_cases h : k ≤ (posPart x).card
  · exact Or.inl (one_le_maxCol c h)
  · exact Or.inr (one_le_maxCol c (by omega))
end KneserColouring
