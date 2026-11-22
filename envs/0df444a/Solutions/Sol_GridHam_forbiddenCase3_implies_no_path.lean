-- Prove2me | solution 1 for GridHam.forbiddenCase3_implies_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:50.607798+00:00
-- url     : https://prove2.me/submissions/9cbbaffb-7868-4a90-a160-b85a6535b629

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_GridHam_g3_no_path
public import Theorems.Thm_GridHam_forbiddenCase3_iff
public import Theorems.Thm_GridHam_hasHamPath_transpose


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h3 : width = 3 ∨ height = 3) (hf : ForbiddenCase3 width height s t) :
    ¬ HasHamPath width height s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < width ∧ sy < height := hs
  have ht' : tx < width ∧ ty < height := ht
  rw [forbiddenCase3_iff] at hf
  unfold F3A at hf
  rcases hf with ⟨hw3, hg⟩ | ⟨hw3, hg⟩
  · subst hw3
    have hg' : G3 height sy ty sx ((sy + sx) % 2) ((ty + tx) % 2) := by
      rw [Nat.add_comm sy sx, Nat.add_comm ty tx]
      exact hg
    intro hp
    exact g3_no_path height sy sx ty tx ⟨hs'.2, hs'.1⟩ ⟨ht'.2, ht'.1⟩ hg'
      (hasHamPath_transpose hp)
  · have hh3 : height = 3 := by omega
    subst hh3
    exact g3_no_path width sx sy tx ty hs' ht' hg
end GridHam
