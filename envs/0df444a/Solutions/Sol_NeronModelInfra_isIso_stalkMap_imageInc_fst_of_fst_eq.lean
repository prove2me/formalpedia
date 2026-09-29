-- Prove2me | solution 1 for NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bc156803-6296-5678-ad24-c70cf51cf275

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace DomGC6

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isOpenImmersion_sι : IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine (isLocalization_iff (Submonoid.powers ϖ) K).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      exact isUnit_iff_ne_zero.mpr
        ((IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr (pow_ne_zero n hϖ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨⟨a * ↑v⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have hbK : algebraMap R K b ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hbK, ← map_mul, ← map_mul, hv]
      congr 1
      rw [mul_assoc, ← mul_assoc (↑v⁻¹ : R), Units.inv_mul, one_mul]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective R K h]⟩
  rw [specGenericFibreInclusion_eq]
  exact IsOpenImmersion.of_isLocalization ϖ

theorem mem_range_sι_of_ne_closedPoint (t : ↥(Spec (CommRingCat.of R)))
    (ht : t ≠ IsLocalRing.closedPoint R) : t ∈ Set.range (specGenericFibreInclusion R K).base := by
  have hbot : t.asIdeal = ⊥ := by
    by_contra hne
    apply ht
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R K) ⊥ = t.asIdeal
  rw [hbot, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)]

end DomGC6

open DomGC6 in
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
    [IsIntegral Y₁]
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K))
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁) :
    IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η) := by
  obtain ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ := hf₁
  obtain ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ := hf₂
  haveI := he₁
  haveI := he₂
  haveI hI : IsOpenImmersion (specGenericFibreInclusion R K) := isOpenImmersion_sι K

  let p₁ := pullback.fst f₁ (specGenericFibreInclusion R K)
  let π := δ.imageι ≫ pullback.fst f₁ f₂

  have hgenpt : f₁.base (genericPoint Y₁) ≠ IsLocalRing.closedPoint R := by
    intro h

    obtain ⟨θ, hθξ, hθ⟩ := Flat.generalizingMap f₁
      (show (⟨⊥, Ideal.isPrime_bot⟩ : ↥(Spec (CommRingCat.of R))) ⤳ f₁.base ξ₁ from by
        rw [hξ₁, ← PrimeSpectrum.le_iff_specializes]; exact bot_le)
    have h1 : f₁.base (genericPoint Y₁) ⤳ f₁.base θ := (genericPoint_specializes θ).map f₁.continuous
    rw [h, hθ] at h1
    have h2 := ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).closure_eq ▸
      (specializes_iff_mem_closure.mp h1) : (⟨⊥, Ideal.isPrime_bot⟩ : ↥(Spec (CommRingCat.of R))) ∈
        ({IsLocalRing.closedPoint R} : Set _))
    have h3 := congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp h2)
    exact IsDiscreteValuationRing.not_a_field R h3.symm
  haveI : Nonempty ↥(pullback f₁ (specGenericFibreInclusion R K)) := by
    have : genericPoint Y₁ ∈ Set.range p₁.base := by
      rw [Scheme.Pullback.range_fst]
      exact mem_range_sι_of_ne_closedPoint K _ hgenpt
    obtain ⟨z, -⟩ := this
    exact ⟨z⟩
  haveI : IsIntegral (pullback f₁ (specGenericFibreInclusion R K)) := isIntegral_of_isOpenImmersion p₁
  haveI : Nonempty ↥(pullback e₁.1 e₂.1) :=
    ⟨(inv (pullback.fst e₁.1 e₂.1)).base (Classical.arbitrary _)⟩
  haveI hEint : IsIntegral (pullback e₁.1 e₂.1) := isIntegral_of_isOpenImmersion (pullback.fst e₁.1 e₂.1)

  haveI : IsLocallyNoetherian (pullback f₁ (specGenericFibreInclusion R K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f₁ (specGenericFibreInclusion R K))
  haveI : CompactSpace ↥(pullback f₁ (specGenericFibreInclusion R K)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f₁ (specGenericFibreInclusion R K))
  haveI : IsLocallyNoetherian (pullback e₁.1 e₂.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst e₁.1 e₂.1)
  haveI : CompactSpace ↥(pullback e₁.1 e₂.1) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst e₁.1 e₂.1)
  haveI : IsNoetherian (pullback e₁.1 e₂.1) := {}
  haveI : IsLocallyNoetherian (pullback f₁ f₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f₁ f₂ ≫ f₁)
  haveI : QuasiCompact δ := inferInstance

  have hcond : pullback.fst e₁.1 e₂.1 ≫ (p₁ ≫ f₁) =
      (pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) ≫ f₂ := by
    rw [← Category.assoc, ← hδ₁, ← hδ₂, Category.assoc, Category.assoc, pullback.condition]
  let δK : pullback e₁.1 e₂.1 ⟶ pullback (p₁ ≫ f₁) f₂ :=
    pullback.lift (pullback.fst e₁.1 e₂.1) (pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ _) hcond
  let u : pullback (p₁ ≫ f₁) f₂ ⟶ pullback f₁ f₂ :=
    pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])
  have hδKu : δK ≫ u = δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hδ₁]
      change δK ≫ pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂ = _
      rw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hδ₂]
      change δK ≫ pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) _ _ ≫ pullback.snd f₁ f₂ = _
      rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.comp_id]
  haveI : IsClosedImmersion δK := by
    haveI : IsClosedImmersion (δK ≫ pullback.fst (p₁ ≫ f₁) f₂) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsClosedImmersion.of_comp δK (pullback.fst (p₁ ≫ f₁) f₂)
  haveI : IsOpenImmersion u := by dsimp only [u]; infer_instance
  haveI : IsImmersion δ := by rw [← hδKu]; infer_instance

  obtain ⟨hDint, hτgen, hτiso⟩ :=
    AlgebraicGeometry.Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint δ
  haveI := hDint

  have hj : δ.toImage ≫ π = pullback.fst e₁.1 e₂.1 ≫ p₁ := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hδ₁]
  haveI hjo : IsOpenImmersion (δ.toImage ≫ π) := by rw [hj]; infer_instance
  have hgen : π.base (genericPoint δ.image) = genericPoint Y₁ := by
    rw [← hτgen, ← Scheme.Hom.comp_apply]

    have himg := (genericPoint_spec ↥(pullback e₁.1 e₂.1)).image (δ.toImage ≫ π).continuous
    rw [Set.image_univ] at himg
    have hdense : closure (Set.range (δ.toImage ≫ π).base) = Set.univ :=
      ((δ.toImage ≫ π).isOpenEmbedding.isOpen_range.dense
        (Set.range_nonempty _)).closure_eq
    rw [hdense] at himg
    exact himg.eq (genericPoint_spec Y₁)
  have hbir : IsIso (π.stalkMap (genericPoint δ.image)) := by
    rw [← hτgen]
    have hso : IsIso ((δ.toImage ≫ π).stalkMap (genericPoint ↥(pullback e₁.1 e₂.1))) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp hjo).2 (genericPoint ↥(pullback e₁.1 e₂.1))
    haveI := hτiso
    have hc := Scheme.Hom.stalkMap_comp δ.toImage π (genericPoint ↥(pullback e₁.1 e₂.1))
    haveI : IsIso (π.stalkMap (δ.toImage.base (genericPoint ↥(pullback e₁.1 e₂.1))) ≫
        δ.toImage.stalkMap (genericPoint ↥(pullback e₁.1 e₂.1))) := by
      rw [← hc]; exact hso
    exact IsIso.of_isIso_comp_right (π.stalkMap (δ.toImage.base (genericPoint ↥(pullback e₁.1 e₂.1))))
      (δ.toImage.stalkMap (genericPoint ↥(pullback e₁.1 e₂.1)))

  have hηne : η ≠ genericPoint δ.image := by
    intro h
    apply hgenpt
    rw [← hgen, ← h]
    change f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base η)) = _
    rw [hη₁, hξ₁]
  have hπη : π.base η = ξ₁ := by
    change (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁; exact hη₁
  obtain ⟨_, hdvr⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R f₁ (π.base η)
    (by rw [hπη]; exact hξ₁)
    (by
      intro y hy hyk
      rw [hπη] at hy ⊢
      exact (hy.antisymm (hξ₁gen y hyk)).eq)
  haveI := hdvr
  exact AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint π hgen hbir η hηne

end S_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq
end P2MW
export P2MW.S_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq (solution)
