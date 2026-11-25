-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isInvariant_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:22.967794+00:00
-- url     : https://prove2.me/submissions/d0bc3065-d8b1-426f-96fc-0c789fb9803f

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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    π.IsInvariant (LinearMap.ker (T : H →ₗ[ℂ] K)) := by
  intro g v hv
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  rw [hT, hv, map_zero]
end GroundTheory.Automorphic.UnitaryRep
