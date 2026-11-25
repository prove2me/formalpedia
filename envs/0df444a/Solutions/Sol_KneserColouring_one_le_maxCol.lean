-- Prove2me | solution 1 for KneserColouring.one_le_maxCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:22.816577+00:00
-- url     : https://prove2.me/submissions/db729812-5e12-4e31-8cd6-148c7a8621fe

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) {B : Finset (Fin n)}
    (h : k ≤ B.card) : 1 ≤ maxCol c B := by
  obtain ⟨A, hA, hcard⟩ := exists_subset_card_eq h
  have h1 : setCol c A ≤ maxCol c B := le_sup (mem_powersetCard.2 ⟨hA, hcard⟩)
  have h2 : setCol c A = (c ⟨A, hcard⟩).val + 1 := by simp [setCol, hcard]
  omega
end KneserColouring
