-- Prove2me | solution 1 for NashWilliams.edge_eq_of_edgeEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:56.743221+00:00
-- url     : https://prove2.me/submissions/b0745132-4c8f-4cb2-b51e-4f52788f518e

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
theorem _root_.solution {e e' : G.edgeSet} {a b : V}
    (h : edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a))
    (h' : edgeEnds G e' = (a, b) ∨ edgeEnds G e' = (b, a)) : e = e' := by
  apply Subtype.ext
  rw [← mk_edgeEnds G e, ← mk_edgeEnds G e']
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h'] <;> simp [Sym2.eq_swap]
end NashWilliams
