-- Prove2me | solution 1 for MasulloGRH.frechet_quotient_isCompleteTVS
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:09:28.87851+00:00
-- url     : https://prove2.me/submissions/7eab7c9e-3f16-459e-80bb-d662c2da543d

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology

lemma isCauchyFilter_iff_cauchy {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (f : Filter G) :
    IsCauchyFilter f ↔ @Cauchy G (IsTopologicalAddGroup.rightUniformSpace G) f := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  rw [Cauchy, uniformity_eq_comap_nhds_zero' G]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    intro U hU
    obtain ⟨N, hN, hNU⟩ := mem_comap.1 hU
    obtain ⟨A, hA, hAA⟩ := h N hN
    refine mem_prod_same_iff.2 ⟨A, hA, ?_⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hNU
    simp only [Set.mem_preimage]
    have := hAA y hy x hx
    simpa [sub_eq_add_neg] using this
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    intro N hN
    have : (fun p : G × G => p.2 + -p.1) ⁻¹' N ∈ f ×ˢ f := h (preimage_mem_comap hN)
    obtain ⟨A, hA, hAA⟩ := mem_prod_same_iff.1 this
    exact ⟨A, hA, fun x hx y hy => by
      simpa [sub_eq_add_neg] using hAA (Set.mk_mem_prod hy hx)⟩

theorem solution (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (hF : IsFrechet F) (W : Submodule ℂ F) (hW : IsClosed (W : Set F)) :
    IsCompleteTVS (F ⧸ W) := by
  obtain ⟨⟨ι, _, p, hp⟩, ⟨hT2, hc⟩, hmet⟩ := hF
  haveI : IsTopologicalAddGroup F := hp.topologicalAddGroup
  haveI : IsClosed (W : Set F) := hW
  haveI : TopologicalSpace.PseudoMetrizableSpace F := inferInstance
  haveI : FirstCountableTopology F := inferInstance
  haveI hcF : @CompleteSpace F (IsTopologicalAddGroup.rightUniformSpace F) := by
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    refine ⟨fun {f} hf => ?_⟩
    obtain ⟨x, hx⟩ := hc f ((isCauchyFilter_iff_cauchy f).2 hf)
    exact ⟨x, hx⟩
  have hQ : @CompleteSpace (F ⧸ W) (IsTopologicalAddGroup.rightUniformSpace (F ⧸ W)) :=
    QuotientAddGroup.completeSpace_right' F W.toAddSubgroup
  refine ⟨inferInstance, fun f hf => ?_⟩
  letI : UniformSpace (F ⧸ W) := IsTopologicalAddGroup.rightUniformSpace (F ⧸ W)
  obtain ⟨x, hx⟩ := hQ.complete ((isCauchyFilter_iff_cauchy f).1 hf)
  exact ⟨x, hx⟩
