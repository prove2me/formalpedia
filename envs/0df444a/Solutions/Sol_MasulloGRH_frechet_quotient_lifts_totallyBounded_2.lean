-- Prove2me | solution 2 for MasulloGRH.frechet_quotient_lifts_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:08:33.713179+00:00
-- url     : https://prove2.me/submissions/f73108d6-d2db-4838-86b5-4c76cfe892de

import Theorems.Thm_MasulloGRH_frechet_quotient_lifts_precompact

set_option autoImplicit false

open Pointwise MasulloGRH

theorem solution (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : Set (X ⧸ W))
    (hB : ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U) :
    ∃ B' : Set X, Bornology.IsVonNBounded ℂ B' ∧ B ⊆ (W.mkQ : X → X ⧸ W) '' B' := by
  obtain ⟨S, hS, hBS⟩ := frechet_quotient_lifts_precompact X hF W hW B hB
  refine ⟨S, ?_, hBS⟩
  obtain ⟨ι, _, p, hp⟩ := hF.1
  haveI : IsTopologicalAddGroup X := hp.topologicalAddGroup
  haveI : ContinuousSMul ℂ X := hp.continuousSMul
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  haveI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  apply TotallyBounded.isVonNBounded
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨t, ht⟩ := hS U hU
  refine ⟨t, t.finite_toSet, fun x hx => ?_⟩
  obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_add.1 (ht hx)
  exact Set.mem_biUnion ha ⟨u, hu, rfl⟩
