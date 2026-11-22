-- Prove2me | solution 1 for GridHam.colSeg_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:53:17.159359+00:00
-- url     : https://prove2.me/submissions/97be0900-7608-44de-b28b-48ac4a5ab3c2

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo k : ℕ) : (colSeg c lo k).head? = some (c, lo + k) := by
  cases k with
  | zero => rfl
  | succ k => rfl
end GridHam
