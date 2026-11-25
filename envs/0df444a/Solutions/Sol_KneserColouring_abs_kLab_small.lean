-- Prove2me | solution 1 for KneserColouring.abs_kLab_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:33.048877+00:00
-- url     : https://prove2.me/submissions/5e2eb113-5d43-4c68-9716-9ab89a2bec09

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
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    {x : Fin n → SignType} (hx : suppCard x ≤ 2 * k - 2) : |kLab c x| = suppCard x := by
  unfold kLab
  rw [if_pos hx]
  split_ifs <;> simp
end KneserColouring
