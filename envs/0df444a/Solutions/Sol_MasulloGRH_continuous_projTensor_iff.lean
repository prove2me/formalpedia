-- Prove2me | solution 1 for MasulloGRH.continuous_projTensor_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:55:05.978797+00:00
-- url     : https://prove2.me/submissions/880a843b-b0b0-411d-b14a-e196922b34ab

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_continuous_projTensor_iff

/-- Re-indexing a defining family of seminorms by its range: a topology defined by a family of
seminorms indexed by a type in an arbitrary universe is defined by a family indexed by a type in
the universe of the space. -/
theorem isLocallyConvexTopology_of_withSeminorms {X : Type u} [AddCommGroup X] [Module ℂ X]
    (t : TopologicalSpace X) {ι : Type v} [Nonempty ι] (q : SeminormFamily ℂ X ι)
    (hq : @WithSeminorms ℂ X ι _ _ _ q t) : MasulloGRH.IsLocallyConvexTopology X t := by
  let _ : TopologicalSpace X := t
  have : IsTopologicalAddGroup X := hq.topologicalAddGroup
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let q' : SeminormFamily ℂ X (Set.range q) := fun s => s.1
  have : Nonempty (Set.range q) := ⟨⟨q i₀, i₀, rfl⟩⟩
  refine ⟨Set.range q, inferInstance, q', ?_⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at hq ⊢
  rw [hq]
  exact (iInf_range' (fun s : Seminorm ℂ X => (𝓝 (0 : ℝ)).comap s) q).symm

end Sol_MasulloGRH_continuous_projTensor_iff

open MasulloGRH Sol_MasulloGRH_continuous_projTensor_iff

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F)
    (G : Type v) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hG : IsLocallyConvexTopology G ‹TopologicalSpace G›) (T : E ⊗[ℂ] F →ₗ[ℂ] G) :
    @Continuous (E ⊗[ℂ] F) G (projTensorTopology E F) _ T ↔
      Continuous (fun p : E × F => T (p.1 ⊗ₜ[ℂ] p.2)) := by
  -- the hypotheses `hE`, `hF` on `E` and `F` are not needed for this equivalence
  have _ := hE
  have _ := hF
  constructor
  · -- the canonical bilinear map is continuous for the projective topology
    intro hT
    have hten : @Continuous (E × F) (E ⊗[ℂ] F) _ (projTensorTopology E F)
        (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
      unfold projTensorTopology
      exact continuous_sInf_rng.2 fun t ht => ht.2
    exact @Continuous.comp (E × F) (E ⊗[ℂ] F) G _ (projTensorTopology E F) _ _ _ hT hten
  · -- the topology induced by `T` is locally convex and makes `⊗` continuous
    intro hb
    obtain ⟨ι, hι, p, hp⟩ := hG
    have hlc : IsLocallyConvexTopology (E ⊗[ℂ] F)
        (TopologicalSpace.induced T ‹TopologicalSpace G›) :=
      isLocallyConvexTopology_of_withSeminorms _ (p.comp T) (T.withSeminorms_induced hp)
    have hle : projTensorTopology E F ≤ TopologicalSpace.induced T ‹TopologicalSpace G› :=
      sInf_le ⟨hlc, continuous_induced_rng.2 hb⟩
    exact continuous_iff_le_induced.2 hle
