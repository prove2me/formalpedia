-- Prove2me | solution 1 for GridHam.no_prev_of_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:04:22.672389+00:00
-- url     : https://prove2.me/submissions/b5f1648e-4dea-4de5-be91-37210f9caf3e

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_split_unique

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hh : p.head? = some x) (h : PNext p y x) : False := by
  cases p with
  | nil => simp at hh
  | cons a rest =>
    have hax : a = x := by simpa using hh
    subst hax
    obtain ⟨l1, l2, e⟩ := h
    have e' : [] ++ a :: rest = (l1 ++ [y]) ++ a :: l2 := by
      show a :: rest = (l1 ++ [y]) ++ a :: l2
      rw [e]
      simp
    have hnd' : ([] ++ a :: rest).Nodup := hnd
    have hsu := split_unique [] (l1 ++ [y]) rest l2 a hnd' e'
    have hl := congrArg List.length hsu.1
    simp at hl
end GridHam
