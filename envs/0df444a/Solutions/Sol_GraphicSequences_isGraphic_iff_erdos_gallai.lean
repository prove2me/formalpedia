-- Prove2me | solution 1 for GraphicSequences.isGraphic_iff_erdos_gallai
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:45.14708+00:00
-- url     : https://prove2.me/submissions/2093b23a-7c6e-4268-aa80-5ecaf04cbfbe

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Definitions.Def_DegreeSequences_Solution
public import Theorems.Thm_DegreeSequences_isGraphic_iff_erdos_gallai


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open GraphicSequences
namespace GraphicSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k :=
  DegreeSequences.isGraphic_iff_erdos_gallai d hd
end GraphicSequences
