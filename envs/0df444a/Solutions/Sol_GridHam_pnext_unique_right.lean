-- Prove2me | solution 1 for GridHam.pnext_unique_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:52.938229+00:00
-- url     : https://prove2.me/submissions/5f7aa981-ac28-4233-a17f-5d0a52db4609

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_split_unique

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y y' : Coord} (hnd : p.Nodup)
    (h1 : PNext p x y) (h2 : PNext p x y') : y = y' := by
  obtain ⟨l1, l2, e1⟩ := h1
  obtain ⟨l1', l2', e2⟩ := h2
  have hnd' : (l1 ++ x :: y :: l2).Nodup := by rw [← e1]; exact hnd
  have hsu := split_unique l1 l1' (y :: l2) (y' :: l2') x hnd' (e1.symm.trans e2)
  exact (List.cons.inj hsu.2).1
end GridHam
