-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.star_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:21.536315+00:00
-- url     : https://prove2.me/submissions/1a0dc2b7-a3ac-4e11-a5fa-6a80afa6c02c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners

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
theorem _root_.solution {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) :
    star T ∈ π.intertwiners π := by
  rw [star_eq_adjoint]; exact adjoint_mem_intertwiners hT
end GroundTheory.Automorphic.UnitaryRep
