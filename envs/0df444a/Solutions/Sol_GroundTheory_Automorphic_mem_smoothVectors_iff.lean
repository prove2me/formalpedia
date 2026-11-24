-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_smoothVectors_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:58.572804+00:00
-- url     : https://prove2.me/submissions/11f6ab6d-3cfb-43f5-971d-a50b2e252732

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors_iff_le
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset


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
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
namespace GroundTheory.Automorphic
theorem _root_.solution {v : V} :
    v ∈ smoothVectors ρ ↔ ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K := by
  constructor
  · intro hv
    obtain ⟨K, hKc, hKv⟩ :=
      exists_openSubgroup_isCompact_subset (hv.mem_nhds (one_mem (stabilizerOf ρ v)))
    exact ⟨K, hKc, K.isOpen, fun k hk => hKv hk⟩
  · rintro ⟨K, -, hKo, hv⟩
    exact Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hKo
end GroundTheory.Automorphic
