-- Prove2me | solution 1 for GridHam.cnt1_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:24:29.736896+00:00
-- url     : https://prove2.me/submissions/6901f522-4af2-4514-8080-32d9c2b743f1

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (a : Coord) (l : List Coord) :
    cnt1 (a :: l) = cnt1 l + (if parity a = 1 then 1 else 0) := by
  unfold cnt1
  simp [List.countP_cons]
end GridHam
