-- Prove2me | solution 1 for GridHam.pnext_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:04:25.666764+00:00
-- url     : https://prove2.me/submissions/3b8f6247-2070-40a7-9315-4b9c9b130824

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_split_unique

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', R = y :: R' := by
  obtain ⟨l1, l2, e⟩ := h
  have hnd' : (L ++ x :: R).Nodup := by rw [← hp]; exact hnd
  have hsu := split_unique L l1 R (y :: l2) x hnd' (hp.symm.trans e)
  exact ⟨l2, hsu.2⟩
end GridHam
