-- Prove2me | solution 1 for MasulloGRH.strongDual_frechet_isCompleteTVS
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:22:57.804573+00:00
-- url     : https://prove2.me/submissions/63d59df8-c9a7-4f1e-a919-19c34db8bc44

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology
open scoped Uniformity

/-- The strong dual of a Fréchet space is complete.  A Fréchet space is metrizable, hence a
sequential space, and Mathlib's `ContinuousLinearMap.instCompleteSpace` shows that the topology of
uniform convergence on bounded sets is then complete with values in the complete space `ℂ`.  The
mission's Cauchy filters (for the additive structure) are Cauchy for this uniformity. -/
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    IsCompleteTVS (StrongDual ℂ E) := by
  obtain ⟨⟨ι, _, p, hp⟩, -, hmet⟩ := hE
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : TopologicalSpace.MetrizableSpace E := hmet
  have hcomp : CompleteSpace (StrongDual ℂ E) := inferInstance
  refine ⟨inferInstance, fun f hf => ?_⟩
  have hcau : Cauchy f := by
    refine ⟨hf.1, fun V hV => ?_⟩
    rw [uniformity_eq_comap_nhds_zero] at hV
    obtain ⟨U, hU, hUV⟩ := mem_comap.1 hV
    obtain ⟨A, hA, hAU⟩ := hf.2 U hU
    exact mem_of_superset (prod_mem_prod hA hA) fun q hq => hUV (hAU q.2 hq.2 q.1 hq.1)
  exact CompleteSpace.complete hcau
