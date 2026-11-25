-- Prove2me | solution 1 for KneserColouring.maxCol_ne_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:20.627414+00:00
-- url     : https://prove2.me/submissions/a6a8122a-9c3e-4364-a7a3-1d6a5d52a2fd

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_exists_maxCol

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {B1 B2 : Finset (Fin n)} (hd : Disjoint B1 B2) (h1 : 1 ≤ maxCol c B1)
    (heq : maxCol c B1 = maxCol c B2) : False := by
  obtain ⟨A1, hA1, hs1, he1⟩ := exists_maxCol c h1
  obtain ⟨A2, hA2, hs2, he2⟩ := exists_maxCol c (heq ▸ h1)
  have hd' : Disjoint A1 A2 := disjoint_of_subset_left hs1 (disjoint_of_subset_right hs2 hd)
  have hne : (⟨A1, hA1⟩ : {s : Finset (Fin n) // s.card = k}) ≠ ⟨A2, hA2⟩ := by
    intro h
    have h' : A1 = A2 := congrArg Subtype.val h
    subst h'
    have : A1 = ∅ := disjoint_self_iff_empty _ |>.1 hd'
    rw [this, card_empty] at hA1
    omega
  apply hc _ _ hne hd'
  apply Fin.ext
  omega
end KneserColouring
