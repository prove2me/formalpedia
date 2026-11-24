-- Prove2me | solution 1 for GlobalTheory.CutOff.exists_isClopen_isCompact_superset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:37.255797+00:00
-- url     : https://prove2.me/submissions/b49022b0-0668-442f-8798-51251128abb3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff
namespace GlobalTheory.CutOff
theorem _root_.solution {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by
  classical
  have h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V := by
    intro z
    obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
    obtain ⟨V, hV, hzV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKz
    exact ⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩
  choose V hVc hVk hzV using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))
  exact ⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z,
    t.isCompact_biUnion fun z _ => hVk z, ht⟩
end GlobalTheory.CutOff
