-- Prove2me | solution 1 for GridHam.pnext_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:22.944849+00:00
-- url     : https://prove2.me/submissions/722daf46-7141-47ae-a9fe-3c7bd4027c4a

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_pos

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', p = (L ++ [x]) ++ y :: R' := by
  obtain ⟨R', e⟩ := pnext_pos hnd hp h
  exact ⟨R', by rw [hp, e]; simp⟩
end GridHam
