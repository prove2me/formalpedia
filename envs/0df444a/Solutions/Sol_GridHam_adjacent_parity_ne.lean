-- Prove2me | solution 1 for GridHam.adjacent_parity_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:24:06.62567+00:00
-- url     : https://prove2.me/submissions/ee902682-73db-4062-8d08-82aebf69d5c0

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {v w : Coord} (h : Adjacent v w) :
    parity v ≠ parity w := by
  unfold Adjacent at h
  unfold parity
  rcases h with ⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩ <;> omega
end GridHam
