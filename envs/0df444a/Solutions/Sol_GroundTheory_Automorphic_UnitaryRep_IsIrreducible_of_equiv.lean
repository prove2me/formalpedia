-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsIrreducible.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:14.733581+00:00
-- url     : https://prove2.me/submissions/51792c00-1ba8-4a5f-9f15-e87065b2fb86

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
namespace IsIrreducible
theorem _root_.solution (hπ : π.IsIrreducible) (e : π.Equiv σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hπ⟩ := hπ
  refine ⟨e.toLinearIsometryEquiv.toEquiv.nontrivial_congr.mp hnt, fun W hW hWinv => ?_⟩
  let E : H →L[ℂ] K := e.toLinearIsometryEquiv
  have hcl : IsClosed ((W.comap (E : H →ₗ[ℂ] K) : Submodule ℂ H) : Set H) :=
    hW.preimage E.continuous
  have hinv : π.IsInvariant (W.comap (E : H →ₗ[ℂ] K)) := by
    intro g v hv
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [show E (π g v) = σ g (E v) from e.map_apply' g v]
    exact hWinv g _ hv
  have hsurj : Function.Surjective E := e.toLinearIsometryEquiv.surjective
  rcases hπ _ hcl hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := hw
    rw [h, Submodule.mem_bot] at this
    simp [this]
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hsurj w
    have : v ∈ W.comap (E : H →ₗ[ℂ] K) := by rw [h]; exact Submodule.mem_top
    exact this
end IsIrreducible
end GroundTheory.Automorphic.UnitaryRep
