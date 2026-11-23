-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:20.21748+00:00
-- url     : https://prove2.me/submissions/cdd67a4f-e843-410c-9afc-913505b92704

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_map_right

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
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsInvariant
theorem _root_.solution {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant Vᗮ := by
  intro g v hv w hw
  rw [inner_map_right]
  exact hv _ (hV _ _ hw)
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep
