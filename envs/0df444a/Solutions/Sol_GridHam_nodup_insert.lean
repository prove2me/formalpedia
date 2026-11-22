-- Prove2me | solution 1 for GridHam.nodup_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:27:58.188374+00:00
-- url     : https://prove2.me/submissions/96cf9c8e-29d9-40c0-bf71-515faab855b1

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_nodup_append_of
public import Theorems.Thm_GridHam_mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (D : List Coord) (hD : D.Nodup) : ∀ (l1 : List Coord) (a b : Coord)
    (l2 : List Coord), (l1 ++ a :: b :: l2).Nodup → (∀ u ∈ D, u ∉ l1 ++ a :: b :: l2) →
    (l1 ++ a :: (D ++ b :: l2)).Nodup := by
  intro l1
  induction l1 with
  | nil =>
    intro a b l2 h hdisj
    show (a :: (D ++ b :: l2)).Nodup
    have h' : (a :: b :: l2).Nodup := h
    obtain ⟨han, hbl⟩ := List.nodup_cons.mp h'
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hd | hd
      · exact hdisj a hd (by simp)
      · exact han hd
    · apply nodup_append_of D (b :: l2) hD hbl
      intro u hu v hv heq
      apply hdisj u hu
      rw [heq]
      show v ∈ a :: b :: l2
      exact List.mem_cons.mpr (Or.inr hv)
  | cons x l ih =>
    intro a b l2 h hdisj
    show (x :: (l ++ a :: (D ++ b :: l2))).Nodup
    have h' : (x :: (l ++ a :: b :: l2)).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases (mem_insert_iff x l D l2 a b).mp hm with hd | hp
      · exact hdisj x hd (List.mem_cons.mpr (Or.inl rfl))
      · exact hxn hp
    · exact ih a b l2 hrest (fun u hu hm => hdisj u hu (List.mem_cons.mpr (Or.inr hm)))
end GridHam
