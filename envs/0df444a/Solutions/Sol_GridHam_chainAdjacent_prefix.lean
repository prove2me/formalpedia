-- Prove2me | solution 1 for GridHam.chainAdjacent_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:12:50.338097+00:00
-- url     : https://prove2.me/submissions/6fd4f827-734d-494c-81f1-c64695472a16

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 l2 : List Coord),
    chainAdjacent (l1 ++ l2) = true → chainAdjacent l1 = true := by
  intro l1
  induction l1 with
  | nil => intro _ _; rfl
  | cons x l ih =>
    intro l2 h
    cases l with
    | nil => rfl
    | cons y l' =>
      have hc' : (adjacentB x y && chainAdjacent (y :: (l' ++ l2))) = true := by
        simpa [chainAdjacent] using h
      simp at hc'
      obtain ⟨hxy, hcl⟩ := hc'
      have hrec : chainAdjacent (y :: l') = true := ih l2 hcl
      have e : chainAdjacent (x :: y :: l') = (adjacentB x y && chainAdjacent (y :: l')) := rfl
      simp only [e, hxy, hrec, Bool.and_self]
end GridHam
