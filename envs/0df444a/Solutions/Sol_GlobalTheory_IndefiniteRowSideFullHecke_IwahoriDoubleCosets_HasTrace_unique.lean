-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:13.495569+00:00
-- url     : https://prove2.me/submissions/acd8b194-cd14-40a5-8a30-e31544ca48fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IwahoriDoubleCosets_IsIntegralOp_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
namespace HasTrace
theorem _root_.solution {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {c d : ℂ}
    (hc : HasTrace μ π f c) (hd : HasTrace μ π f d) : c = d := by
  obtain ⟨A, hA, -, rfl⟩ := hc
  obtain ⟨B, hB, -, rfl⟩ := hd
  obtain rfl := hA.unique hB
  rfl
end HasTrace
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
