-- Prove2me | solution 1 for GroundTheory.Automorphic.coe_fixedMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:38.863835+00:00
-- url     : https://prove2.me/submissions/8bf38583-1c09-48f6-94f2-4e0d3bef87c8

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
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G)
    (v : fixedVectors ρ H) : (fixedMap ρ f H v : W) = f v := rfl
end GroundTheory.Automorphic
