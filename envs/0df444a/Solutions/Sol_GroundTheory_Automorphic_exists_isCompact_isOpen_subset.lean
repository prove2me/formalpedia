-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_isCompact_isOpen_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.425416+00:00
-- url     : https://prove2.me/submissions/961f535c-f174-456c-9615-d0dd5650ff6c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic
theorem _root_.solution {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨V, hV, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨V, hKc.of_isClosed_subset hV.isClosed hVK, hV.isOpen, hxV, hVK.trans hKU⟩
end GroundTheory.Automorphic
