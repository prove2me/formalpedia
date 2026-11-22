-- Prove2me | solution 1 for GridHam.freeCol_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:16.763968+00:00
-- url     : https://prove2.me/submissions/27b16b0c-a961-42ba-8d71-dda3061677fb

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c h sx sy tx ty : ℕ) (hf : FreeCol c h sx sy tx ty) :
    ∃ y, y < h ∧ (c, y) ≠ (sx, sy) ∧ (c, y) ≠ (tx, ty) := by
  unfold FreeCol at hf
  rcases hf with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨0, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
  · refine ⟨1, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
  · refine ⟨2, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
end GridHam
