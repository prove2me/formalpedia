-- Prove2me | solution 1 for GridHam.mem_allCoords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:28:03.205571+00:00
-- url     : https://prove2.me/submissions/bdf10833-d636-462d-ba61-d61096330b04

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) (v : Coord) :
    v ∈ allCoords w h ↔ v.1 < w ∧ v.2 < h := by
  simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨v.1, hx, v.2, hy, rfl⟩
end GridHam
