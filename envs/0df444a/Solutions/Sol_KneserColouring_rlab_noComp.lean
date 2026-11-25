-- Prove2me | solution 1 for KneserColouring.rlab_noComp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:50.462684+00:00
-- url     : https://prove2.me/submissions/38553997-b8f4-4b73-aa35-675b03fdb5cd

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Theorems.Thm_KneserColouring_pref_ne_zero
public import Theorems.Thm_KneserColouring_pref_le

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {lab : (Fin n → SignType) → ℤ} (hNC : NoCompLab lab) {k : ℕ} {r : Room n}
    (h : IsRoom k r) (hk : k ≤ n) :
    ∀ i ∈ range k, ∀ j ∈ range k, rlab lab r i ≠ -rlab lab r j := by
  intro i hi j hj
  rw [mem_range] at hi hj
  rcases le_total i j with hij | hij
  · exact hNC _ _ (pref_ne_zero h hk hi) (pref_le r (by omega))
  · have h2 := hNC _ _ (pref_ne_zero h hk hj) (pref_le r (show j + 1 ≤ i + 1 by omega))
    unfold rlab
    intro h'
    apply h2
    rw [h']
    ring
end KneserColouring
