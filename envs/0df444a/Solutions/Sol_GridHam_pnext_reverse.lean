-- Prove2me | solution 1 for GridHam.pnext_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:05.94381+00:00
-- url     : https://prove2.me/submissions/408808fb-6a7e-4722-8465-f1bc61967648

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y : Coord} (h : PNext p x y) :
    PNext p.reverse y x := by
  obtain ⟨l1, l2, e⟩ := h
  exact ⟨l2.reverse, l1.reverse, by rw [e]; simp⟩
end GridHam
