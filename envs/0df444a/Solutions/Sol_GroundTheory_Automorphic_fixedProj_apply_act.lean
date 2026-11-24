-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedProj_apply_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:52.782303+00:00
-- url     : https://prove2.me/submissions/3e01cf4b-d0fc-4505-b80b-916ed4bf84ea

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem_coinvariantsKer

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
variable {ρ} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
namespace GroundTheory.Automorphic
theorem _root_.solution {k : G} (hk : k ∈ K) (v : V) :
    fixedProj ρ hρ hKc hKo (ρ k v) = fixedProj ρ hρ hKc hKo v := by
  rw [← sub_eq_zero, ← map_sub]
  exact fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo (sub_mem_coinvariantsKer hk v)
end GroundTheory.Automorphic
