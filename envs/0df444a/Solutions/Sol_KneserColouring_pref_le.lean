-- Prove2me | solution 1 for KneserColouring.pref_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:12.680395+00:00
-- url     : https://prove2.me/submissions/6467d9a5-8b48-4c1d-a835-35c6e1e08045

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
theorem _root_.solution (r : Room n) {i j : ℕ} (hij : i ≤ j) :
    ∀ c, pref r i c ≠ 0 → pref r i c = pref r j c := by
  intro c hc
  simp only [pref] at hc ⊢
  by_cases h1 : (r.2 c).val < i
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1] at hc
    exact absurd rfl hc
end KneserColouring
