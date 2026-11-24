-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.isLocallyConstant_indicator_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:47:01.586497+00:00
-- url     : https://prove2.me/submissions/e5ddfee5-fb11-4f06-aad8-f2f9fea41ae7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac GlobalTheory.LocFlat.CFac.Span
namespace GlobalTheory.LocFlat.CFac.Span
theorem _root_.solution {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
end GlobalTheory.LocFlat.CFac.Span
