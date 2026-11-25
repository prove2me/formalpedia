-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.map_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:07.483918+00:00
-- url     : https://prove2.me/submissions/d0a8f1c8-5be4-4735-946e-cf498dc8974f

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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (g : G) : Function.Injective (π g) := fun v w h => by
  have := congrArg (π g⁻¹) h
  rwa [map_inv_apply_map, map_inv_apply_map] at this
end GroundTheory.Automorphic.UnitaryRep
