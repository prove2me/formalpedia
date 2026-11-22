-- Prove2me | solution 1 for GridHam.mem_allCoords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:11.448817+00:00
-- url     : https://prove2.me/submissions/982654ac-3a96-4e9b-bd20-4282aff7c435

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

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
