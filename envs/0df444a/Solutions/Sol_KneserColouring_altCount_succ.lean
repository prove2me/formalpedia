-- Prove2me | solution 1 for KneserColouring.altCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:40.503073+00:00
-- url     : https://prove2.me/submissions/9d988303-9de6-4eb1-826d-8fe2423ffd49

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_card_sphere
public import Theorems.Thm_KneserColouring_card_boundaryPairs
public import Theorems.Thm_KneserColouring_doorPairs_mod_two
public import Theorems.Thm_KneserColouring_even_card_flipPairs
public import Theorems.Thm_KneserColouring_even_card_swapPairs


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    altCount lab (k + 1) % 2 = altCount lab k % 2 := by
  have h1 := doorPairs_mod_two lab hNC (K := k + 1) (by omega) hkn
  obtain ⟨a, ha⟩ := even_card_swapPairs lab hkn
  obtain ⟨b, hb⟩ := even_card_flipPairs lab hkn
  have hB1 := card_boundaryPairs lab hkn
  have hS := card_sphere lab hanti hNC hk1 (by omega)
  have s1 := card_filter_add_card_filter_not (s := doorPairs lab (k + 1)) (fun p => p.2 < k)
  have s2 := card_filter_add_card_filter_not
    (s := (doorPairs lab (k + 1)).filter (fun p => ¬ p.2 < k))
    (fun p : Room n × ℕ => p.1.2 ⟨k, by omega⟩ ≠ ⟨k, by omega⟩)
  omega
end KneserColouring
