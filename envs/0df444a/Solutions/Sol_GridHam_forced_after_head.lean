-- Prove2me | solution 1 for GridHam.forced_after_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:07:41.321014+00:00
-- url     : https://prove2.me/submissions/ebbbc907-ad93-4ec9-9931-f9c5b080ef9e

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_mem_left
public import Theorems.Thm_GridHam_pnext_mem_right
public import Theorems.Thm_GridHam_pnext_adj
public import Theorems.Thm_GridHam_no_prev_of_head
public import Theorems.Thm_GridHam_interior_two
public import Theorems.Thm_GridHam_adjacent_symm


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {u x z : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hh : p.head? = some u) (hx : x ∈ p)
    (hxh : p.head? ≠ some x) (hxl : p.getLast? ≠ some x)
    (hnb : ∀ y ∈ p, Adjacent y x → y = u ∨ y = z) : PNext p u x := by
  obtain ⟨a, b, hab, hpa, hpb⟩ := interior_two hnd hx hxh hxl
  have ha := hnb a (pnext_mem_left hpa) (pnext_adj hch hpa)
  have hb := hnb b (pnext_mem_right hpb) (adjacent_symm (pnext_adj hch hpb))
  rcases ha with ha | ha
  · rw [ha] at hpa
    exact hpa
  · rcases hb with hb | hb
    · rw [hb] at hpb
      exact (no_prev_of_head hnd hh hpb).elim
    · exact absurd (ha.trans hb.symm) hab
end GridHam
