-- Prove2me | solution 1 for NashWilliams.edgeEnds_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:11:03.926165+00:00
-- url     : https://prove2.me/submissions/2a4bc03b-8932-4837-9eb1-44ab88be4837

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_mk_edgeEnds

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution {e : G.edgeSet} {a b : V} (h : (e : Sym2 V) = s(a, b)) :
    edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a) := by
  have := mk_edgeEnds G e
  rw [h] at this
  rcases (Sym2.mk_eq_mk_iff (q := (a, b))).1 this with h | h
  · exact Or.inl h
  · exact Or.inr h
end NashWilliams
