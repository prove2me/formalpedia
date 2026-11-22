-- Prove2me | solution 1 for GridHam.suff_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:42.684299+00:00
-- url     : https://prove2.me/submissions/2b3cafdc-7e98-4bc2-a47d-bbab5e1d2491

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_suff_step

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ n, SuffP n
  | 0 => by
    intro w h s t hsz hs _ _ _
    have hs0 : s.1 < w ∧ s.2 < h := hs
    omega
  | n + 1 => suff_step n (solution n)
end GridHam
