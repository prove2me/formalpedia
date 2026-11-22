-- Prove2me | solution 1 for GridHam.colSeg_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:24:48.433247+00:00
-- url     : https://prove2.me/submissions/3cde6612-0983-4ddd-8c73-376b35598a3b

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo : ℕ) : ∀ k, (colSeg c lo k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((c, lo + (k + 1)) :: colSeg c lo k).length = k + 1 + 1
    rw [List.length_cons, ih]
end GridHam
