-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:45.892943+00:00
-- url     : https://prove2.me/submissions/8327e0f5-2be1-4723-ac24-3025e0002101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_mem_S

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
theorem _root_.solution : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y],
    Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  intro X Y _ _ _ _ _ _ _ _
  have hmap : (Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2)).map
      (SB (X × Y)).subtype = S X Y := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  rintro F -
  have h := mem_S F.1 F.2
  rw [← hmap] at h
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 h
  have : G = F := Subtype.ext hGF
  rwa [← this]
end GlobalTheory.LocFlat.CFac.Span
