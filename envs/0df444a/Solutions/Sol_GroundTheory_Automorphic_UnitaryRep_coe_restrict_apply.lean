-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:37.858555+00:00
-- url     : https://prove2.me/submissions/7eeed59a-2757-4df7-929a-6504a743356b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
variable {π}
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}
variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := rfl
end GroundTheory.Automorphic.UnitaryRep
