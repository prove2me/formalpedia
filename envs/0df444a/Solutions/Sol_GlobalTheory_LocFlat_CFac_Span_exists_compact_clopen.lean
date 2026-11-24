-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.exists_compact_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:59.879341+00:00
-- url     : https://prove2.me/submissions/c59ae73f-f95e-4caa-ae6c-54dc886e3362

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
theorem _root_.solution [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hO hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).isOpen_iff.1
    isOpen_interior x hxK
  exact ⟨V, hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), hV, hxV,
    (hVK.trans interior_subset).trans hKO⟩
end GlobalTheory.LocFlat.CFac.Span
