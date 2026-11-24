-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:20.912981+00:00
-- url     : https://prove2.me/submissions/683047c4-3e4d-4ece-8568-6a7d29a9a020

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
    v ∈ fixedVectors ρ H ↔ ∀ h ∈ H, ρ h v = v := Iff.rfl
end GroundTheory.Automorphic
