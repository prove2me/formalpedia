-- Prove2me | solution 1 for GridHam.pnext_mem_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:37:59.887257+00:00
-- url     : https://prove2.me/submissions/0b65cca6-1fa3-4fe8-aa14-e4f406ee78aa

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y : Coord} (h : PNext p x y) : x ∈ p := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e]
  simp
end GridHam
