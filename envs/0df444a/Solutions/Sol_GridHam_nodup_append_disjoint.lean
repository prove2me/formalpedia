-- Prove2me | solution 1 for GridHam.nodup_append_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:04:55.584373+00:00
-- url     : https://prove2.me/submissions/7a1f9fb7-d097-4bf8-b094-1a6cb7cfb468

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup →
    ∀ c ∈ l1, c ∉ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ c hc; simp at hc
  | cons x l ih =>
    intro l2 h c hc hc2
    have h' : (x :: (l ++ l2)).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    rcases List.mem_cons.mp hc with e | e
    · rw [e] at hc2
      exact hxn (List.mem_append.mpr (Or.inr hc2))
    · exact ih l2 hrest c e hc2
end GridHam
