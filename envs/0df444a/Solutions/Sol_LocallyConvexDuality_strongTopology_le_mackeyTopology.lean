-- Prove2me | solution 1 for LocallyConvexDuality.strongTopology_le_mackeyTopology
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:56:27.807543+00:00
-- url     : https://prove2.me/submissions/b3b7769d-5052-48ae-b100-5164bf45261a

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

open LocallyConvexDuality

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    strongTopology B ≤ mackeyTopology B := by
  -- Both topologies on `E` are induced by the same map `x ↦ (y ↦ B x y)` from a topology of
  -- uniform convergence on a family of subsets of `F`; it suffices to compare the two families.
  unfold strongTopology mackeyTopology polarTopology
  -- Uniform convergence on a larger family of sets is a finer uniform structure
  -- (`UniformOnFun.mono`), hence a finer topology, and `induced` is monotone.
  refine induced_mono (UniformSpace.toTopologicalSpace_mono (UniformOnFun.mono le_rfl ?_))
  -- Every absolutely convex `σ(F, E)`-compact set is `σ(F, E)`-bounded: a compact subset of a
  -- topological vector space is von Neumann bounded.
  intro A hA
  exact IsCompact.isVonNBounded (E := WeakBilin B.flip) 𝕜 hA.2
