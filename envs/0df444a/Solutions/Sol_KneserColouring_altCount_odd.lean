-- Prove2me | solution 1 for KneserColouring.altCount_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:50.988802+00:00
-- url     : https://prove2.me/submissions/f68e448f-add4-43d3-8017-e943ebccda32

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_altCount_succ
public import Theorems.Thm_KneserColouring_altCount_one

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) : ∀ k, 1 ≤ k → k ≤ n → altCount lab k % 2 = 1 := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [altCount_one lab]
  | succ k hk ih =>
    intro hkn
    rw [altCount_succ lab hanti hNC hk hkn]
    exact ih (by omega)
end KneserColouring
