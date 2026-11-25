-- Prove2me | solution 1 for KneserColouring.pref_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:51.861073+00:00
-- url     : https://prove2.me/submissions/a8c2bee8-b455-438a-9259-be770951e636

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
theorem _root_.solution {r r' : Room n} {i : ℕ} (h1 : ∀ c, (r.2 c).val < i ↔ (r'.2 c).val < i)
    (h2 : ∀ c, (r.2 c).val < i → r.1 c = r'.1 c) : pref r i = pref r' i := by
  funext c
  simp only [pref]
  by_cases hc : (r.2 c).val < i
  · rw [if_pos hc, if_pos ((h1 c).1 hc), h2 c hc]
  · rw [if_neg hc, if_neg (fun h => hc ((h1 c).2 h))]
end KneserColouring
