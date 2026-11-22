-- Prove2me | solution 1 for GridHam.nodup_map_coord_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:16.274854+00:00
-- url     : https://prove2.me/submissions/15bb7441-f409-4bc0-9d59-673f591b7a82

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, f v = f u → v = u) → l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hinj hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    show (f a :: l.map f).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a :=
        hinj w (List.mem_cons.mpr (Or.inr hw)) a (List.mem_cons.mpr (Or.inl rfl)) hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih (fun v hv u hu =>
        hinj v (List.mem_cons.mpr (Or.inr hv)) u (List.mem_cons.mpr (Or.inr hu))) hndt
end GridHam
