-- Prove2me | solution 1 for MazurTransfer.continuous_equivariant_cocycle_lift
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T23:47:07.217862+00:00
-- url     : https://prove2.me/submissions/0c1f4e62-35bd-4e33-819e-ac923fe55c76

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. -/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.Group.Basic

theorem solution
    (G M N : Type*) [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology N]
    (i : M →* N) (hi : Function.Injective i)
    (he : ∀ (g : G) (m : M), i (g • m) = g • i m)
    (z : G → N) (hz : groupCohomology.IsMulCocycle₁ z) (hc : Continuous z)
    (hrange : ∀ g : G, ∃ m : M, i m = z g) :
    ∃ w : G → M, Continuous w ∧ groupCohomology.IsMulCocycle₁ w ∧
      ∀ g : G, i (w g) = z g := by
  classical
  let r : N → M := fun n => if h : ∃ m : M, i m = n then Classical.choose h else 1
  have hr (n : N) (hn : ∃ m : M, i m = n) : i (r n) = n := by
    dsimp [r]
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  refine ⟨r ∘ z, (continuous_of_discreteTopology : Continuous r).comp hc, ?_, ?_⟩
  · intro g h
    apply hi
    change i (r (z (g * h))) = i (g • r (z h) * r (z g))
    rw [map_mul, he, hr _ (hrange (g * h)), hr _ (hrange h), hr _ (hrange g)]
    exact hz g h
  · intro g
    exact hr _ (hrange g)

#print axioms solution
