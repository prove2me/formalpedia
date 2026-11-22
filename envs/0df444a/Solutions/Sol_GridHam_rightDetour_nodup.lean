-- Prove2me | solution 1 for GridHam.rightDetour_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:28:56.405811+00:00
-- url     : https://prove2.me/submissions/941ab513-327c-4c58-930e-78c812eeeaed

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_nodup_append_of
public import Theorems.Thm_GridHam_mem_colSeg
public import Theorems.Thm_GridHam_colSeg_nodup

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h y : ℕ) (_hy : y + 1 < h) : (rightDetour w h y).Nodup := by
  unfold rightDetour
  apply nodup_append_of _ _ (colSeg_nodup w 0 y)
  · apply nodup_append_of _ _ (List.nodup_reverse.mpr (colSeg_nodup (w + 1) 0 (h - 1)))
      (colSeg_nodup w (y + 1) _)
    intro u hu v hv heq
    rw [List.mem_reverse, mem_colSeg] at hu
    rw [mem_colSeg] at hv
    rw [heq] at hu
    omega
  · intro u hu v hv heq
    rw [mem_colSeg] at hu
    rw [List.mem_append, List.mem_reverse, mem_colSeg, mem_colSeg] at hv
    rw [heq] at hu
    omega
end GridHam
