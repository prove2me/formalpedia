-- Prove2me | solution 1 for GridHam.stripDown_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:22.174922+00:00
-- url     : https://prove2.me/submissions/ae8246c3-c1fa-4eb9-b3be-42ac35120d67

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_hasHamPath_transpose
public import Theorems.Thm_GridHam_stripLeft_preserves

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.2) (ht : 2 ≤ t.2)
    (hfree : ∃ x, x < width ∧ (x, 2) ≠ s ∧ (x, 2) ≠ t)
    (h : HasHamPath width (height - 2) (s.1, s.2 - 2) (t.1, t.2 - 2)) :
    HasHamPath width height s t := by
  obtain ⟨x, hx, hxs, hxt⟩ := hfree
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    stripLeft_preserves height width (swapXY s) (swapXY t) hs ht
      ⟨x, hx, fun heq => hxs (congrArg swapXY heq), fun heq => hxt (congrArg swapXY heq)⟩
      (hasHamPath_transpose h)
  exact hasHamPath_transpose hT
end GridHam
