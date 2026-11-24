-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedProj_apply_of_mem_coinvariantsKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:35.845798+00:00
-- url     : https://prove2.me/submissions/5a90653c-3eee-408e-8c35-0825575d39e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep

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
theorem _root_.solution {v : V} (hv : v ∈ coinvariantsKer ρ K) :
    fixedProj ρ hρ hKc hKo v = 0 :=
  (Submodule.projectionOnto_apply_eq_zero_iff _).2 hv
end GroundTheory.Automorphic
