-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:08:32.225862+00:00
-- url     : https://prove2.me/submissions/b5b970ef-d324-4fee-8c13-858310d63598

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_isLocallyConstant_indicator_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac GlobalTheory.LocFlat.CFac.Span
namespace GlobalTheory.LocFlat.CFac.Span
theorem _root_.solution {Z : Type} [TopologicalSpace Z] {W : Set Z} (hc : IsCompact W)
    (hW : IsClopen W) : W.indicator (1 : Z → ℂ) ∈ SB Z :=
  ⟨isLocallyConstant_indicator_one hW, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.LocFlat.CFac.Span
