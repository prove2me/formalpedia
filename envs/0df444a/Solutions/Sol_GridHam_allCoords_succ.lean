-- Prove2me | solution 1 for GridHam.allCoords_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:22.275106+00:00
-- url     : https://prove2.me/submissions/07664f59-93ca-4559-b658-eee088b02b68

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) :
    allCoords (w + 1) h = allCoords w h ++ (List.range h).map (fun y => (w, y)) := by
  simp [allCoords, List.range_succ]
end GridHam
