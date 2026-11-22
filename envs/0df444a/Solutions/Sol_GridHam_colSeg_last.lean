-- Prove2me | solution 1 for GridHam.colSeg_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:22:57.028253+00:00
-- url     : https://prove2.me/submissions/f28e7955-97bd-4490-be59-3b62cea5a914

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo : ℕ) : ∀ k, (colSeg c lo k).getLast? = some (c, lo) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      show (colSeg c lo (k' + 1)).getLast? = some (c, lo)
      exact ih
end GridHam
