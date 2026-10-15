-- Prove2me | solution 1 for MazurTransfer.discrete_equivariant_quotient_continuous_smul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T23:33:12.930296+00:00
-- url     : https://prove2.me/submissions/63df69b7-4813-4b8b-9c65-6d4678a280ef

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. -/
import Mathlib.Topology.Algebra.MulAction

theorem solution
    (G X Y : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction G X] [TopologicalSpace X] [ContinuousSMul G X]
    [MulAction G Y] [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (hf : Continuous f) (hs : Function.Surjective f)
    (he : ∀ (g : G) (x : X), f (g • x) = g • f x) : ContinuousSMul G Y := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have hc : Continuous (fun g : G => g • f x) := by
    have hh : (fun g : G => g • f x) = (fun g : G => f (g • x)) :=
      funext (fun g => (he g x).symm)
    rw [hh]
    exact hf.comp (continuous_id.smul continuous_const)
  exact IsOpen.preimage hc (isOpen_discrete {f x})

#print axioms solution
