-- Prove2me | solution 1 for GridHam.nodup_map_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:51:42.865258+00:00
-- url     : https://prove2.me/submissions/4ac3495d-0533-4656-943f-f1c25fc073ea

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) (hf : ∀ v w, f v = f w → v = w) :
    ∀ (l : List Coord), l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    show (f a :: l.map f).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a := hf w a hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih hndt
end GridHam
