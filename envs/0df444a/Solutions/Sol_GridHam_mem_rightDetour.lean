-- Prove2me | solution 1 for GridHam.mem_rightDetour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:28:08.046168+00:00
-- url     : https://prove2.me/submissions/c8407ef3-7993-4c3b-b1c1-e245240dd29c

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_colSeg

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h y : ℕ) (hy : y + 1 < h) (u : Coord) :
    u ∈ rightDetour w h y ↔ (u.1 = w ∧ u.2 < h) ∨ (u.1 = w + 1 ∧ u.2 < h) := by
  unfold rightDetour
  simp only [List.mem_append, List.mem_reverse, mem_colSeg]
  constructor
  · intro hu
    omega
  · intro hu
    omega
end GridHam
