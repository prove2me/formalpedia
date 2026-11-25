-- Prove2me | solution 1 for KneserColouring.one_le_suppCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:31.096346+00:00
-- url     : https://prove2.me/submissions/3111938f-0b1e-4ea2-bc21-b66b51e1d785

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
theorem _root_.solution {x : Fin n → SignType} (hx : x ≠ 0) : 1 ≤ suppCard x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
end KneserColouring
