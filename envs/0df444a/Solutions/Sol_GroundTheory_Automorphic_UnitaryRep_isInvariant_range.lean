-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isInvariant_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:24.012017+00:00
-- url     : https://prove2.me/submissions/c89698e0-8739-4230-ba30-6de737d72948

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
    σ.IsInvariant (LinearMap.range (T : H →ₗ[ℂ] K)) := by
  rintro g _ ⟨v, rfl⟩
  exact ⟨π g v, hT g v⟩
end GroundTheory.Automorphic.UnitaryRep
