-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_fixedVectors_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:51.485873+00:00
-- url     : https://prove2.me/submissions/2000d5ad-e5c7-41d9-9237-0d500b9630a1

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable {ρ}
namespace GroundTheory.Automorphic
theorem _root_.solution {H : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ H ↔ H ≤ stabilizerOf ρ v := Iff.rfl
end GroundTheory.Automorphic
