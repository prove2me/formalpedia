-- Prove2me | solution 2 for MasulloGRH.strongDual_frechet_isCompleteTVS
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:24:15.531323+00:00
-- url     : https://prove2.me/submissions/3b00ccb0-0db6-4405-87e6-0eb08373acc7

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Topology

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    IsCompleteTVS (StrongDual ℂ E) := by
  obtain ⟨⟨ι, _, p, hp⟩, _, hM⟩ := hE
  haveI := hp.topologicalAddGroup
  haveI := hp.continuousSMul
  haveI : SequentialSpace E := inferInstance
  haveI : CompleteSpace (StrongDual ℂ E) := inferInstance
  refine ⟨inferInstance, fun f hf => ?_⟩
  obtain ⟨hne, hU⟩ := hf
  apply CompleteSpace.complete
  refine ⟨hne, ?_⟩
  intro V hV
  rw [uniformity_eq_comap_nhds_zero] at hV
  obtain ⟨U, hU0, hUV⟩ := hV
  obtain ⟨A, hA, hAU⟩ := hU U hU0
  refine Filter.mem_of_superset (Filter.prod_mem_prod hA hA) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact hUV (hAU y hy x hx)
