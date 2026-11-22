-- Prove2me | solution 1 for GridHam.next_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:33:28.783492+00:00
-- url     : https://prove2.me/submissions/ce6d2cde-e323-4b19-9768-c1fde8adbd81

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_mem_right
public import Theorems.Thm_GridHam_pnext_adj
public import Theorems.Thm_GridHam_pnext_unique_left
public import Theorems.Thm_GridHam_interior_two

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {a x b : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hx : x ∈ p) (hxh : p.head? ≠ some x)
    (hxl : p.getLast? ≠ some x) (hprev : PNext p a x)
    (hnb : ∀ y ∈ p, Adjacent x y → y = a ∨ y = b) : PNext p x b := by
  obtain ⟨a', b', hab, hpa, hpb⟩ := interior_two hnd hx hxh hxl
  have ha' : a' = a := pnext_unique_left hnd hpa hprev
  rcases hnb b' (pnext_mem_right hpb) (pnext_adj hch hpb) with hb | hb
  · exact absurd (ha'.trans hb.symm) hab
  · rw [hb] at hpb
    exact hpb
end GridHam
