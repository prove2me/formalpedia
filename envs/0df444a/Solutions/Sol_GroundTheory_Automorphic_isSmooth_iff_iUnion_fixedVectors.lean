-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_iff_iUnion_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:16.423058+00:00
-- url     : https://prove2.me/submissions/666a8443-256a-4b4d-b89f-b50ea46e1dc9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists

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
    IsSmooth ρ ↔ ⋃ (K : Subgroup G) (_ : IsCompact (K : Set G)) (_ : IsOpen (K : Set G)),
      (fixedVectors ρ K : Set V) = univ := by
  rw [isSmooth_iff_forall_exists, eq_univ_iff_forall]
  simp only [mem_iUnion, SetLike.mem_coe, exists_prop]
end GroundTheory.Automorphic
