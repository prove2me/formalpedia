-- Prove2me | solution 1 for KneserColouring.adjSwap_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:29.89014+00:00
-- url     : https://prove2.me/submissions/92a2e9d5-b47b-4106-b938-855ba33374b9

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {j : ℕ} (h : j + 1 < n) (c : Fin n) :
    (adjSwap n j c).val = if c.val = j then j + 1 else if c.val = j + 1 then j else c.val := by
  simp only [adjSwap, h, ↓reduceDIte, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]
end KneserColouring
