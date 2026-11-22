-- Prove2me | solution 1 for GridHam.adjacent_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:52:20.673572+00:00
-- url     : https://prove2.me/submissions/064de3d5-2984-4089-9820-1bc0a6e39007

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {v w : Coord} (h : Adjacent v w) : Adjacent w v := by
  unfold Adjacent at h ⊢
  omega
end GridHam
