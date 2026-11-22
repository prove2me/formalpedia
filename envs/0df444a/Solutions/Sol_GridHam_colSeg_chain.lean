-- Prove2me | solution 1 for GridHam.colSeg_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:25:54.941864+00:00
-- url     : https://prove2.me/submissions/e099b666-823b-4cc7-afec-e46ba5a92d80

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_cons
public import Theorems.Thm_GridHam_colSeg_head

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo : ℕ) : ∀ k, chainAdjacent (colSeg c lo k) = true := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    exact chainAdjacent_cons (c, lo + (k + 1)) (c, lo + k) (colSeg c lo k) (colSeg_head c lo k)
      (by unfold Adjacent; dsimp only; omega) ih
end GridHam
