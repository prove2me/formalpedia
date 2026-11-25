-- Prove2me | solution 1 for GraphicSequences.isGraphic_iff_havel_hakimi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:16:44.960812+00:00
-- url     : https://prove2.me/submissions/fa95bfff-4870-4b4a-8418-fdde4cec9f43

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Definitions.Def_DegreeSequences_Solution
public import Theorems.Thm_DegreeSequences_isGraphic_iff_havel_hakimi


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open GraphicSequences
namespace GraphicSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ d 0 ≤ m ∧ (∀ j : Fin m, j.val < d 0 → 1 ≤ d j.succ) ∧
      IsGraphic (havelHakimi d) :=
  DegreeSequences.isGraphic_iff_havel_hakimi d hd
end GraphicSequences
