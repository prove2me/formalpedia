-- Prove2me | solution 1 for GridHam.nodup_not_mem_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:10:09.847183+00:00
-- url     : https://prove2.me/submissions/9d31f88a-fdeb-4122-835e-e84919336b15

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (m : List Coord) (t : Coord), (m ++ [t]).Nodup → t ∉ m := by
  intro m
  induction m with
  | nil => intro t _; simp
  | cons x m' ih =>
    intro t h
    have h' : (x :: (m' ++ [t])).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    intro hm
    rcases List.mem_cons.mp hm with e | e
    · apply hxn
      rw [← e]
      simp
    · exact ih t hrest e
end GridHam
