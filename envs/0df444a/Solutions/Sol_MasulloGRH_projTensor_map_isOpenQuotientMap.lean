-- Prove2me | solution 1 for MasulloGRH.projTensor_map_isOpenQuotientMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:34:23.943295+00:00
-- url     : https://prove2.me/submissions/64efdc0e-6e67-4e80-be75-ec18721b5020

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_projTensor_nhds_zero_hasBasis
import Theorems.Thm_MasulloGRH_continuous_projTensor_iff

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

open scoped ComplexOrder

open MasulloGRH

namespace Sol_MasulloGRH_projTensor_map_isOpenQuotientMap

/-- The infimum of a set of locally convex topologies on a complex vector space is a locally
convex topology: it is defined by the family of all seminorms that are continuous for it. -/
theorem isLocallyConvexTopology_sInf {X : Type u} [AddCommGroup X] [Module ℂ X]
    (ts : Set (TopologicalSpace X)) (h : ∀ t ∈ ts, IsLocallyConvexTopology X t) :
    IsLocallyConvexTopology X (sInf ts) := by
  have hP : @PolynormableSpace ℂ X _ _ _ (sInf ts) := by
    refine PolynormableSpace.sInf ?_
    intro t ht
    obtain ⟨ι, _, p, hp⟩ := h t ht
    let _ : TopologicalSpace X := t
    exact hp.toPolynormableSpace
  let _ : TopologicalSpace X := sInf ts
  exact ⟨{p : Seminorm ℂ X // Continuous p}, ⟨⟨0, continuous_const⟩⟩, _,
    PolynormableSpace.withSeminorms ℂ X⟩

section

variable (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The projective topology is locally convex. -/
theorem isLocallyConvexTopology_projTensor :
    IsLocallyConvexTopology (E ⊗[ℂ] F) (projTensorTopology E F) :=
  isLocallyConvexTopology_sInf _ fun _ ht => ht.1

/-- The canonical bilinear map is continuous for the projective topology. -/
theorem continuous_tmul_projTensor :
    @Continuous (E × F) (E ⊗[ℂ] F) _ (projTensorTopology E F) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  unfold projTensorTopology
  exact continuous_sInf_rng.2 fun t ht => ht.2

/-- The projective topology is a group topology. -/
theorem isTopologicalAddGroup_projTensor :
    @IsTopologicalAddGroup (E ⊗[ℂ] F) (projTensorTopology E F) _ := by
  obtain ⟨ι, _, p, hp⟩ := isLocallyConvexTopology_projTensor E F
  let _ : TopologicalSpace (E ⊗[ℂ] F) := projTensorTopology E F
  exact hp.topologicalAddGroup

end

/-- The image of an absolutely convex set under a linear map is absolutely convex. -/
theorem absConvex_image {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (f : X →ₗ[ℂ] Y) {s : Set X} (hs : AbsConvex ℂ s) :
    AbsConvex ℂ (f '' s) := by
  refine ⟨balanced_iff_smul_mem.2 ?_, hs.2.linear_image f⟩
  rintro a ha _ ⟨x, hx, rfl⟩
  exact ⟨a • x, balanced_iff_smul_mem.1 hs.1 ha hx, map_smul f a x⟩

end Sol_MasulloGRH_projTensor_map_isOpenQuotientMap

open Sol_MasulloGRH_projTensor_map_isOpenQuotientMap

theorem solution (E₁ E₂ : Type u) (F₁ F₂ : Type v)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂) (hF₁ : IsHLCS F₁) (hF₂ : IsHLCS F₂)
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂)
    (h₁ : IsOpenQuotientMap T₁) (h₂ : IsOpenQuotientMap T₂) :
    @IsOpenQuotientMap (E₁ ⊗[ℂ] E₂) (F₁ ⊗[ℂ] F₂) (projTensorTopology E₁ E₂)
      (projTensorTopology F₁ F₂) (TensorProduct.map T₁.toLinearMap T₂.toLinearMap) := by
  let _ : TopologicalSpace (E₁ ⊗[ℂ] E₂) := projTensorTopology E₁ E₂
  let _ : TopologicalSpace (F₁ ⊗[ℂ] F₂) := projTensorTopology F₁ F₂
  have : IsTopologicalAddGroup (E₁ ⊗[ℂ] E₂) := isTopologicalAddGroup_projTensor E₁ E₂
  have : IsTopologicalAddGroup (F₁ ⊗[ℂ] F₂) := isTopologicalAddGroup_projTensor F₁ F₂
  refine ⟨?_, ?_, ?_⟩
  · -- surjectivity is algebraic
    exact TensorProduct.map_surjective h₁.surjective h₂.surjective
  · -- continuity: universal property of `E₁ ⊗_π E₂`
    refine (continuous_projTensor_iff E₁ E₂ hE₁ hE₂ (F₁ ⊗[ℂ] F₂)
      (isLocallyConvexTopology_projTensor F₁ F₂) _).2 ?_
    have hcomp : (fun p : E₁ × E₂ =>
        TensorProduct.map T₁.toLinearMap T₂.toLinearMap (p.1 ⊗ₜ[ℂ] p.2)) =
        (fun q : F₁ × F₂ => q.1 ⊗ₜ[ℂ] q.2) ∘ Prod.map T₁ T₂ := by
      funext p
      simp
    rw [hcomp]
    exact (continuous_tmul_projTensor F₁ F₂).comp (T₁.continuous.prodMap T₂.continuous)
  · -- openness: the image of a basic neighbourhood of `0` contains a basic neighbourhood of `0`
    refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.2 ?_
    intro S hS
    rw [Filter.mem_map] at hS
    obtain ⟨⟨U, V⟩, ⟨hU, hV⟩, hsub⟩ :=
      (projTensor_nhds_zero_hasBasis E₁ E₂ hE₁ hE₂).mem_iff.1 hS
    have hU' : T₁ '' U ∈ 𝓝 (0 : F₁) := by
      have := h₁.isOpenMap.image_mem_nhds hU
      rwa [map_zero] at this
    have hV' : T₂ '' V ∈ 𝓝 (0 : F₂) := by
      have := h₂.isOpenMap.image_mem_nhds hV
      rwa [map_zero] at this
    refine (projTensor_nhds_zero_hasBasis F₁ F₂ hF₁ hF₂).mem_iff.2
      ⟨(T₁ '' U, T₂ '' V), ⟨hU', hV'⟩, ?_⟩
    have himg : TensorProduct.map T₁.toLinearMap T₂.toLinearMap ''
        absConvexHull ℂ (Set.image2 (fun x y => x ⊗ₜ[ℂ] y) U V) ⊆ S :=
      Set.image_subset_iff.2 hsub
    refine (absConvexHull_min ?_ (absConvex_image _ absConvex_absConvexHull)).trans himg
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x ⊗ₜ[ℂ] y, subset_absConvexHull ⟨x, hx, y, hy, rfl⟩, by simp⟩
