-- Prove2me | solution 1 for GridHam.forbiddenCase2_implies_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:44:59.567993+00:00
-- url     : https://prove2.me/submissions/0174b771-a8a9-40f5-b317-3214f6da2592

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_GridHam_f2_width2_no_path
public import Theorems.Thm_GridHam_f2_height2_no_path
public import Theorems.Thm_GridHam_forbiddenCase2_iff


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hf : ForbiddenCase2 width height s t) :
    ¬ HasHamPath width height s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < width ∧ sy < height := hs
  have ht' : tx < width ∧ ty < height := ht
  rw [forbiddenCase2_iff] at hf
  unfold F2A cornerA at hf
  obtain ⟨hcs, _, hrc⟩ := hf
  rcases hrc with ⟨hw, hrow⟩ | ⟨hh, hcol⟩
  · subst hw
    exact f2_width2_no_path height (sx, sy) (tx, ty) hs' ht' hrow (by show 0 < sy; omega)
      (by show sy + 1 < height; omega)
  · subst hh
    exact f2_height2_no_path width (sx, sy) (tx, ty) hs' ht' hcol (by show 0 < sx; omega)
      (by show sx + 1 < width; omega)
end GridHam
