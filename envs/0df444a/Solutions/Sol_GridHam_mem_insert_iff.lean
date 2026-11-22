-- Prove2me | solution 1 for GridHam.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:35:26.10466+00:00
-- url     : https://prove2.me/submissions/ec63ed20-0ebe-4085-aa0e-4f62a2e7d424

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (u : Coord) (l1 D l2 : List Coord) (a b : Coord) :
    u ∈ l1 ++ a :: (D ++ b :: l2) ↔ u ∈ D ∨ u ∈ l1 ++ a :: b :: l2 := by
  simp only [List.mem_append, List.mem_cons]
  tauto
end GridHam
