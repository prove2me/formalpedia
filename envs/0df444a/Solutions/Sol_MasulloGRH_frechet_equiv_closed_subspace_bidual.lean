-- Prove2me | solution 1 for MasulloGRH.frechet_equiv_closed_subspace_bidual
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:37:05.967822+00:00
-- url     : https://prove2.me/submissions/2fda1251-3564-4b3b-b9ce-a63748bc8ed2

import Theorems.Thm_MasulloGRH_frechet_equiv_subspace_bidual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ V : Submodule ℂ (StrongDual ℂ (StrongDual ℂ E)),
      IsClosed (V : Set (StrongDual ℂ (StrongDual ℂ E))) ∧ Nonempty (E ≃L[ℂ] V) := by
  obtain ⟨ι, hι, p, hp⟩ := hE.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : T2Space E := hE.2.1.1
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := by
    constructor
    intro f hf
    apply hE.2.1.2 f
    obtain ⟨hne, ht⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).mp hf
    refine ⟨hne, ?_⟩
    intro U hU
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp (ht hU)
    refine ⟨A ∩ B, inter_mem hA hB, ?_⟩
    intro x hx y hy
    exact hAB (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)
  obtain ⟨V, ⟨e⟩⟩ := MasulloGRH.frechet_equiv_subspace_bidual E hE
  let j : E →L[ℂ] StrongDual ℂ (StrongDual ℂ E) := V.subtypeL.comp e.toContinuousLinearMap
  have hj : IsEmbedding j := V.isEmbedding_subtypeL.comp e.toHomeomorph.isEmbedding
  have hjU : IsUniformEmbedding j := AddMonoidHom.isUniformEmbedding_of_isEmbedding hj
  have hrange : Set.range j = (V : Set (StrongDual ℂ (StrongDual ℂ E))) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).property
    · intro hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  refine ⟨V, ?_, ⟨e⟩⟩
  rw [← hrange]
  exact hjU.isClosedEmbedding.isClosed_range
