-- Prove2me | solution 1 for GridHam.acc_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:01.387877+00:00
-- url     : https://prove2.me/submissions/c1134712-90cc-4dc7-a87c-9600ef56abd6

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
public import Theorems.Thm_GridHam_colorCompatible_iff
public import Theorems.Thm_GridHam_isForbidden_iff

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) (s t : Coord) :
    IsAcceptable w h s t ↔ AccA w h s.1 s.2 t.1 t.2 := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  show IsAcceptable w h (sx, sy) (tx, ty) ↔ AccA w h sx sy tx ty
  unfold IsAcceptable AccA
  rw [colorCompatible_iff, isForbidden_iff]
end GridHam
