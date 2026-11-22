-- Prove2me | solution 1 for GridHam.colSeg_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:25:03.416648+00:00
-- url     : https://prove2.me/submissions/a007a96b-c37f-4633-903f-a8fd64529b61

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_colSeg

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo : ℕ) : ∀ k, (colSeg c lo k).Nodup := by
  intro k
  induction k with
  | zero => simp [colSeg]
  | succ k ih =>
    show ((c, lo + (k + 1)) :: colSeg c lo k).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    have h := (mem_colSeg c lo k _).mp hm
    dsimp only at h
    omega
end GridHam
