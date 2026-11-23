-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.comp_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:36.260606+00:00
-- url     : https://prove2.me/submissions/5ac2959a-d52c-487d-938a-98ccd95dfadc

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
theorem _root_.solution {S : K →L[ℂ] L} {T : H →L[ℂ] K} (hS : S ∈ σ.intertwiners τ)
    (hT : T ∈ π.intertwiners σ) : S ∘L T ∈ π.intertwiners τ := fun g v => by
  simp [hT g v, hS g (T v)]
end GroundTheory.Automorphic.UnitaryRep
