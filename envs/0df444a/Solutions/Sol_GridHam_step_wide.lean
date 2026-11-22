-- Prove2me | solution 1 for GridHam.step_wide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:49:51.820822+00:00
-- url     : https://prove2.me/submissions/b709a0a9-542f-423f-bf88-99bb33330cd3

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_step_normalized
public import Theorems.Thm_GridHam_accA_swap
public import Theorems.Thm_GridHam_acc_iff
public import Theorems.Thm_GridHam_hasHamPath_reverse


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (n : ℕ) (IH : SuffP n) (w h : ℕ) (s t : Coord)
    (hsz : w + h ≤ n + 1) (hwh : h ≤ w)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t := by
  by_cases hle : s.1 ≤ t.1
  · exact step_normalized n IH w h s t hsz hwh hle hs ht hst hacc
  · have hacc' : IsAcceptable w h t s :=
      (acc_iff w h t s).mpr ((accA_swap w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
    exact hasHamPath_reverse
      (step_normalized n IH w h t s hsz hwh (by omega) ht hs (Ne.symm hst) hacc')
end GridHam
