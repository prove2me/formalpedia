-- Prove2me | solution 1 for LocallyConvexDuality.polarTopology_finite_eq_weak
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:52:50.200837+00:00
-- url     : https://prove2.me/submissions/887995a3-16a0-4401-877e-e698ebd8dd93

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

open LocallyConvexDuality

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    polarTopology B {A : Set F | A.Finite} =
      (inferInstance : TopologicalSpace (WeakBilin B)) := by
  -- On `F → 𝕜`, uniform convergence on finite sets is the product (pointwise) topology:
  -- `UniformOnFun.toFun` is a topological embedding into `F → 𝕜`.
  have hemb : (UniformOnFun.topologicalSpace F 𝕜 {A : Set F | A.Finite}) =
      TopologicalSpace.induced (UniformOnFun.toFun {A : Set F | A.Finite})
        (Pi.topologicalSpace : TopologicalSpace (F → 𝕜)) :=
    (UniformOnFun.isEmbedding_toFun_finite F 𝕜).eq_induced
  -- Hence the polar topology is induced from the product topology by `x ↦ (y ↦ B x y)`,
  -- which is by definition the topology of `WeakBilin B`.
  rw [polarTopology, hemb, induced_compose]
  rfl
