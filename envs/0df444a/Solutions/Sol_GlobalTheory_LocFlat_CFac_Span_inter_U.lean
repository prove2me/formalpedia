-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.inter_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:17.888508+00:00
-- url     : https://prove2.me/submissions/244fde83-8fc7-4e6e-8d2e-554b2dd4339c

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
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.LocFlat.CFac.Span
theorem _root_.solution (r : Set X × Set Y) (L : List (Set X × Set Y)) :
    r.1 ×ˢ r.2 ∩ U L = U (L.map fun s => (r.1 ∩ s.1, r.2 ∩ s.2)) := by
  ext p
  simp only [U, Set.mem_inter_iff, Set.mem_iUnion, List.mem_map, Set.mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, s, hs, h3, h4⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, s, hs, h3, h4⟩
end GlobalTheory.LocFlat.CFac.Span
