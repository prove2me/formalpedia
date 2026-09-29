-- Prove2me | solution 1 for NeronModelInfra.isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4c5d2f9a-7e5c-5978-b02a-2755f248f7ab

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) :
    IsOpenImmersion δ.toImage ∧
      Set.range δ.toImage.base =
        {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R} ∧
      Set.range δ.imageι.base = closure (Set.range δ.base) := by
  classical
  obtain ⟨_, hsep₁, _, hqc₁⟩ := hf₁
  obtain ⟨_, hsep₂, _, hqc₂⟩ := hf₂
  haveI := he₁; haveI := he₂

  have hc : pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      δ ≫ pullback.fst f₁ f₂ := hδ₁.symm
  let c : pullback e₁.1 e₂.1 ⟶ pullback (pullback.fst f₁ (specGenericFibreInclusion R K)) (pullback.fst f₁ f₂) :=
    pullback.lift (pullback.fst e₁.1 e₂.1) δ hc
  have hc₁ : c ≫ pullback.fst _ _ = pullback.fst e₁.1 e₂.1 := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = δ := pullback.lift_snd _ _ _

  have : IsClosedImmersion (c ≫ pullback.fst (pullback.fst f₁ (specGenericFibreInclusion R K))
      (pullback.fst f₁ f₂)) := by rw [hc₁]; infer_instance
  have hcci : IsClosedImmersion c := IsClosedImmersion.of_comp c (pullback.fst _ _)

  have hδimm : IsImmersion δ := by rw [← hc₂]; infer_instance
  have hδqc : QuasiCompact δ := by rw [← hc₂]; infer_instance
  refine ⟨inferInstance, ?_, ?_⟩
  swap
  ·
    change Set.range δ.ker.subschemeι = closure (Set.range δ)
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  ·
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hrange := NeronModelInfra.range_specGenericFibreInclusion_eq_basicOpen R K hϖ

    have hgen : ∀ q : PrimeSpectrum R, q ≠ IsLocalRing.closedPoint R ↔
        q ∈ Set.range (specGenericFibreInclusion R K).base := by
      intro q
      rw [hrange]
      change q ≠ IsLocalRing.closedPoint R ↔ q ∈ PrimeSpectrum.basicOpen ϖ
      rw [PrimeSpectrum.mem_basicOpen]
      constructor
      · intro hq hmem
        apply hq
        apply PrimeSpectrum.ext
        change q.asIdeal = IsLocalRing.maximalIdeal R
        refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top ?_).symm
        rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
        exact hmem
      · rintro hq rfl
        apply hq
        change ϖ ∈ IsLocalRing.maximalIdeal R
        rw [hϖ.maximalIdeal_eq]
        exact Ideal.mem_span_singleton_self ϖ
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      show f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base (δ.toImage.base x))) ≠ _
      have e1 : δ.imageι.base (δ.toImage.base x) = δ.base x := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
      have hm : δ ≫ pullback.fst f₁ f₂ ≫ f₁ = pullback.fst e₁.1 e₂.1 ≫
          pullback.snd f₁ (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K := by
        rw [← Category.assoc, hδ₁, Category.assoc, pullback.condition]
      have e2 : f₁.base ((pullback.fst f₁ f₂).base (δ.base x)) =
          (specGenericFibreInclusion R K).base ((pullback.snd f₁ (specGenericFibreInclusion R K)).base
            ((pullback.fst e₁.1 e₂.1).base x)) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply,
          Scheme.Hom.comp_apply]
      rw [e1, e2]
      exact (hgen _).mpr ⟨_, rfl⟩
    · intro d hd
      change f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ _ at hd

      have h1 : (pullback.fst f₁ f₂).base (δ.imageι.base d) ∈
          Set.range (pullback.fst f₁ (specGenericFibreInclusion R K)).base := by
        rw [Scheme.Pullback.range_fst]
        exact (hgen _).mp hd
      have h2 : δ.imageι.base d ∈ Set.range (pullback.snd (pullback.fst f₁ (specGenericFibreInclusion R K))
          (pullback.fst f₁ f₂)).base := by
        rw [Scheme.Pullback.range_snd]
        exact h1

      have h3 : δ.imageι.base d ∈ closure (Set.range δ.base) := by
        rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨d, rfl⟩

      have h4 : δ.imageι.base d ∈ Set.range δ.base := by
        obtain ⟨u, hu⟩ := h2
        have hq₂ := (pullback.snd (pullback.fst f₁ (specGenericFibreInclusion R K))
          (pullback.fst f₁ f₂)).isOpenEmbedding
        have hcl : IsClosed (Set.range c.base) := c.isClosedEmbedding.isClosed_range
        have : Set.range δ.base = (pullback.snd (pullback.fst f₁ (specGenericFibreInclusion R K))
            (pullback.fst f₁ f₂)).base '' Set.range c.base := by
          rw [← Set.range_comp, ← hc₂]
          rfl
        rw [this] at h3 ⊢
        have hu' : u ∈ closure (Set.range c.base) := by
          rw [hq₂.isEmbedding.closure_eq_preimage_closure_image, Set.mem_preimage, hu]
          exact h3
        rw [hcl.closure_eq] at hu'
        exact ⟨u, hu', hu⟩
      obtain ⟨x, hx⟩ := h4
      refine ⟨x, δ.imageι.isClosedEmbedding.injective ?_⟩
      rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

end S_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
end P2MW
export P2MW.S_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre (solution)
