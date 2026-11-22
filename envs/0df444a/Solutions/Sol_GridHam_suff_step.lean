-- Prove2me | solution 1 for GridHam.suff_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:05.476894+00:00
-- url     : https://prove2.me/submissions/081f7fc5-133c-4144-9a4d-6a1fd09e30ac

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_step_wide
public import Theorems.Thm_GridHam_accA_transpose
public import Theorems.Thm_GridHam_acc_iff
public import Theorems.Thm_GridHam_hasHamPath_transpose


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (n : ℕ) (IH : SuffP n) : SuffP (n + 1) := by
  intro w h s t hsz hs ht hst hacc
  by_cases hwh : h ≤ w
  · exact step_wide n IH w h s t hsz hwh hs ht hst hacc
  · have hs0 : s.1 < w ∧ s.2 < h := hs
    have ht0 : t.1 < w ∧ t.2 < h := ht
    have hsT : InBounds h w (swapXY s) := show s.2 < h ∧ s.1 < w from ⟨hs0.2, hs0.1⟩
    have htT : InBounds h w (swapXY t) := show t.2 < h ∧ t.1 < w from ⟨ht0.2, ht0.1⟩
    have hstT : swapXY s ≠ swapXY t := fun e => hst (congrArg swapXY e)
    have haccT : IsAcceptable h w (swapXY s) (swapXY t) :=
      (acc_iff h w (swapXY s) (swapXY t)).mpr
        ((accA_transpose w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
    exact hasHamPath_transpose
      (step_wide n IH h w (swapXY s) (swapXY t) (by omega) (by omega) hsT htT hstT haccT)
end GridHam
