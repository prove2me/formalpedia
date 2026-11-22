-- Prove2me | solution 1 for GridHam.chainAdjacent_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:52.387049+00:00
-- url     : https://prove2.me/submissions/65a715cb-212d-4417-82fc-5370ff497bac

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_tail

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 m : List Coord),
    chainAdjacent (l1 ++ m) = true → chainAdjacent m = true := by
  intro l1
  induction l1 with
  | nil => intro m h; exact h
  | cons x l ih => intro m h; exact ih m (chainAdjacent_tail x (l ++ m) h)
end GridHam
