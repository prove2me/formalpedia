-- Prove2me | solution 2 for MasulloGRH.frechet_quotient_isCompleteTVS
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:09:31.126384+00:00
-- url     : https://prove2.me/submissions/48e1688f-7322-4834-9de7-81972aab625b

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology Set
open scoped Uniformity

/-- The quotient of a Fréchet space by a closed subspace is complete and Hausdorff
(Bourbaki, *General Topology* IX.3.1 Prop. 4, via `QuotientAddGroup.completeSpace_right'`). -/
theorem solution (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (hF : IsFrechet F) (W : Submodule ℂ F) (hW : IsClosed (W : Set F)) :
    IsCompleteTVS (F ⧸ W) := by
  obtain ⟨⟨ι, _, p, hp⟩, ⟨_, hcomp⟩, hmet⟩ := hF
  have : IsTopologicalAddGroup F := hp.topologicalAddGroup
  have : TopologicalSpace.MetrizableSpace F := hmet
  have : IsClosed (W.toAddSubgroup : Set F) := hW
  have hT2 : T2Space (F ⧸ W) := QuotientAddGroup.instT2Space
  refine ⟨hT2, ?_⟩
  -- completeness of `F` for its translation-invariant uniformity
  have hcF : @CompleteSpace F (IsTopologicalAddGroup.rightUniformSpace F) := by
    let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {q : F × F | q.2 - q.1 ∈ U} ∈ uniformity F := by
      rw [uniformity_eq_comap_nhds_zero F]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (mk_mem_prod hy hx)⟩
  have hcQ : @CompleteSpace (F ⧸ W.toAddSubgroup)
      (IsTopologicalAddGroup.rightUniformSpace (F ⧸ W.toAddSubgroup)) :=
    QuotientAddGroup.completeSpace_right' F W.toAddSubgroup
  -- translate the mission's Cauchy filters on the quotient
  intro f hf
  let _ : UniformSpace (F ⧸ W) := IsTopologicalAddGroup.rightUniformSpace (F ⧸ W)
  have : IsUniformAddGroup (F ⧸ W) := isUniformAddGroup_of_addCommGroup
  have hcau : Cauchy f := by
    refine ⟨hf.1, fun V hV => ?_⟩
    rw [uniformity_eq_comap_nhds_zero] at hV
    obtain ⟨U, hU, hUV⟩ := mem_comap.1 hV
    obtain ⟨A, hA, hAU⟩ := hf.2 U hU
    exact mem_of_superset (prod_mem_prod hA hA) fun q hq => hUV (hAU q.2 hq.2 q.1 hq.1)
  exact hcQ.complete hcau
