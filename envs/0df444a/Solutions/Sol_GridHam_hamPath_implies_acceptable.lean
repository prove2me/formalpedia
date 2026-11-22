-- Prove2me | solution 1 for GridHam.hamPath_implies_acceptable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:56:49.336977+00:00
-- url     : https://prove2.me/submissions/5690ebcf-d0ab-48dc-852e-6f634b6ab3bf

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_GridHam_forbiddenCase2_implies_no_path
public import Theorems.Thm_GridHam_forbiddenCase3_implies_no_path
public import Theorems.Thm_GridHam_forbiddenCase1_implies_no_path
public import Theorems.Thm_GridHam_hamPath_implies_colorCompatible


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h : HasHamPath width height s t) :
    IsAcceptable width height s t := by
  refine ⟨hamPath_implies_colorCompatible width height s t h, ?_⟩
  intro hforb
  unfold IsForbidden at hforb
  split_ifs at hforb with h1 h2 h3
  · exact forbiddenCase1_implies_no_path width height s t hs ht h1 hforb h
  · exact forbiddenCase2_implies_no_path width height s t hs ht hforb h
  · exact forbiddenCase3_implies_no_path width height s t hs ht h3 hforb h
end GridHam
