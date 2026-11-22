-- Prove2me | solution 1 for GridHam.stripUp_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:07.715014+00:00
-- url     : https://prove2.me/submissions/9f4f4ccd-ceb8-4d39-a1e6-e3565511d5c8

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_hasHamPath_transpose
public import Theorems.Thm_GridHam_stripRight_preserves

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : s.2 + 2 < height) (ht : t.2 + 2 < height)
    (hfree : ∃ x, x < width ∧ (x, height - 3) ≠ s ∧ (x, height - 3) ≠ t)
    (h : HasHamPath width (height - 2) s t) :
    HasHamPath width height s t := by
  obtain ⟨x, hx, hxs, hxt⟩ := hfree
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    stripRight_preserves height width (swapXY s) (swapXY t) hs ht
      ⟨x, hx, fun heq => hxs (congrArg swapXY heq), fun heq => hxt (congrArg swapXY heq)⟩
      (hasHamPath_transpose h)
  exact hasHamPath_transpose hT
end GridHam
