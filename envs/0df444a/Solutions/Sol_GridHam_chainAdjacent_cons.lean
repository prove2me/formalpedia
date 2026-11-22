-- Prove2me | solution 1 for GridHam.chainAdjacent_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:35:03.125977+00:00
-- url     : https://prove2.me/submissions/d0efba68-45eb-4892-90e0-45b9b08c9502

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (x y : Coord) (l : List Coord) (hh : l.head? = some y)
    (hadj : Adjacent x y) (hl : chainAdjacent l = true) : chainAdjacent (x :: l) = true := by
  cases l with
  | nil => simp at hh
  | cons z rest =>
    have hzy : z = y := by simpa using hh
    have hA : adjacentB x z = true := by
      unfold adjacentB
      rw [hzy]
      exact decide_eq_true hadj
    have e : chainAdjacent (x :: z :: rest) = (adjacentB x z && chainAdjacent (z :: rest)) := rfl
    simp only [e, hA, hl, Bool.and_self]
end GridHam
