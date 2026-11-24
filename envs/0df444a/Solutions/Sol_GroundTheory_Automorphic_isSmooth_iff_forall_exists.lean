-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_iff_forall_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:39.836686+00:00
-- url     : https://prove2.me/submissions/37fec497-7deb-41a9-990e-fb491300bc43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_mem_smoothVectors_iff

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
theorem _root_.solution :
    IsSmooth ρ ↔ ∀ v : V, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K :=
  forall_congr' fun _ => mem_smoothVectors_iff ρ
end GroundTheory.Automorphic
