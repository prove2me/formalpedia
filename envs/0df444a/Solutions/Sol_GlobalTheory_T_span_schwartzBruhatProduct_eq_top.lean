-- Prove2me | solution 1 for GlobalTheory.T.span_schwartzBruhatProduct_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:23.694987+00:00
-- url     : https://prove2.me/submissions/e0e39f87-c5c0-4474-afcc-d95f4e19ff93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTopStatement
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_span_prodSB_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y], Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  first | exact @GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | exact GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | (intros; apply GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top <;> assumption)
end _root_.GlobalTheory.T
