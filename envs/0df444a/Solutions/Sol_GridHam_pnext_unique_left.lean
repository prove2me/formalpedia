-- Prove2me | solution 1 for GridHam.pnext_unique_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:53.624986+00:00
-- url     : https://prove2.me/submissions/f979cf2b-7ce1-4ecf-84aa-11873fef8d73

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
    (h1 : PNext p y x) (h2 : PNext p y' x) : y = y' := by
  obtain ⟨l1, l2, e1⟩ := h1
  obtain ⟨l1', l2', e2⟩ := h2
  have e1' : p = (l1 ++ [y]) ++ x :: l2 := by rw [e1]; simp
  have e2' : p = (l1' ++ [y']) ++ x :: l2' := by rw [e2]; simp
  have hnd' : ((l1 ++ [y]) ++ x :: l2).Nodup := by rw [← e1']; exact hnd
  have hsu := split_unique (l1 ++ [y]) (l1' ++ [y']) l2 l2' x hnd' (e1'.symm.trans e2')
  have hh := congrArg List.getLast? hsu.1
  simpa using hh
end GridHam
