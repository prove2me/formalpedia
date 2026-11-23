-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.IsBox.inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:59.340804+00:00
-- url     : https://prove2.me/submissions/7da00a44-c1ee-4e4a-acde-92a1880505c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop

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
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.LocFlat.CFac.Span
namespace IsBox
theorem _root_.solution {r s : Set X × Set Y} (hr : IsBox r) (hs : IsBox s) :
    IsBox (r.1 ∩ s.1, r.2 ∩ s.2) :=
  ⟨hr.1.inter_right hs.2.1.isClosed, hr.2.1.inter hs.2.1, hr.2.2.1.inter_right hs.2.2.2.isClosed,
    hr.2.2.2.inter hs.2.2.2⟩
end IsBox
end GlobalTheory.LocFlat.CFac.Span
