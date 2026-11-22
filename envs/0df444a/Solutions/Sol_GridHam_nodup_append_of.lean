-- Prove2me | solution 1 for GridHam.nodup_append_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:40:06.291424+00:00
-- url     : https://prove2.me/submissions/30f46549-650b-475d-a71b-9a3a776f3cf2

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 l2 : List Coord), l1.Nodup → l2.Nodup →
    (∀ v ∈ l1, ∀ w ∈ l2, v ≠ w) → (l1 ++ l2).Nodup := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2 _; simpa using h2
  | cons x l ih =>
    intro l2 h1 h2 hd
    obtain ⟨hxn, hl⟩ := List.nodup_cons.mp h1
    show (x :: (l ++ l2)).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hxn h
      · exact hd x (List.mem_cons.mpr (Or.inl rfl)) x h rfl
    · exact ih l2 hl h2 (fun v hv w hw => hd v (List.mem_cons.mpr (Or.inr hv)) w hw)
end GridHam
