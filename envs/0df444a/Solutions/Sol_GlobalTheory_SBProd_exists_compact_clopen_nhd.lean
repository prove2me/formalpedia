-- Prove2me | solution 1 for GlobalTheory.SBProd.exists_compact_clopen_nhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:44.837478+00:00
-- url     : https://prove2.me/submissions/c6f366a8-73ee-4ae7-8972-9d4a173c0c2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.SBProd
namespace GlobalTheory.SBProd
theorem _root_.solution {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set H, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVs⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds xs)
  exact ⟨V, hV, comp.of_isClosed_subset hV.1 (hVs.trans interior_subset), hxV,
    (hVs.trans interior_subset).trans sU⟩
end GlobalTheory.SBProd
