-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpLower.card_filter_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:31.163571+00:00
-- url     : https://prove2.me/submissions/69347d54-9a0c-4711-9533-44e4e1c282d2

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset
namespace GlobalTheory.CompanionTheory.GapOpLower
theorem _root_.solution {α : Type} [Fintype α] [Zero α] :
    (((univ : Finset α).filter (fun a => a ≠ 0)).card : ℝ) = (Fintype.card α : ℝ) - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ≠ 0)
  have h0 : ((univ : Finset α).filter (fun a => ¬ a ≠ 0)).card = 1 := by
    have : (univ : Finset α).filter (fun a => ¬ a ≠ 0) = {0} := by
      ext a; simp
    rw [this, card_singleton]
  rw [h0, card_univ] at h
  rw [← h]; push_cast; ring
end GlobalTheory.CompanionTheory.GapOpLower
