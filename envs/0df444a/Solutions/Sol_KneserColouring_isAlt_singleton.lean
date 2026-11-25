-- Prove2me | solution 1 for KneserColouring.isAlt_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:20.243882+00:00
-- url     : https://prove2.me/submissions/fabf4179-d6b0-4277-9e5a-4ca864a30486

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (a : ℤ) : IsAlt 0 {a} ∨ IsAlt 1 {a} := by
  have hf : ({a} : Finset ℤ).filter (fun c => |c| < |a|) = ∅ := by
    rw [filter_singleton]
    exact if_neg (lt_irrefl _)
  rcases lt_or_ge 0 a with h | h
  · left
    intro b hb
    rw [mem_singleton] at hb
    subst hb
    rw [hf]
    simp [h]
  · right
    intro b hb
    rw [mem_singleton] at hb
    subst hb
    rw [hf]
    simp
    omega
end KneserColouring
