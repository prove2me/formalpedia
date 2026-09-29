-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/355f9c46-f60b-51e0-8949-1ce1f1e40e12

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

private theorem codim1Local_isLocalizationAway
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K where
  map_units := by
    rintro ⟨y, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero))
  surj := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨(a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩), ?_⟩
    have hu : algebraMap R K u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr u.ne_zero
    have hϖK : algebraMap R K (ϖ ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero)
    have huinv : algebraMap R K ↑u⁻¹ = (algebraMap R K u)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    simp only [map_mul, huinv]
    field_simp
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using IsFractionRing.injective R K h⟩

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := codim1Local_isLocalizationAway R K hϖ
  haveI hoi : IsOpenImmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]; exact IsOpenImmersion.of_isLocalization ϖ

  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  haveI : IsNoetherian T := {}
  haveI : IsReduced T := by
    haveI : ∀ x : T, _root_.IsReduced (T.presheaf.stalk x) := fun x =>
      haveI := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
        R t x).1
      inferInstance
    exact isReduced_of_isReduced_stalk T

  obtain ⟨hdom, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R t η hηs hgen
  let ξ : T := (T.fromSpecStalk η).base ⟨⊥, Ideal.isPrime_bot⟩
  have hξη : ξ ⤳ η := by
    have : ξ ∈ Set.range (T.fromSpecStalk η).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have hξne : ξ ≠ η := by
    intro h
    have h2 : (T.fromSpecStalk η).base (IsLocalRing.closedPoint (T.presheaf.stalk η)) = η :=
      Scheme.fromSpecStalk_closedPoint
    have h3 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (T.presheaf.stalk η)) =
        IsLocalRing.closedPoint (T.presheaf.stalk η) :=
      (T.fromSpecStalk η).isEmbedding.injective (h.trans h2.symm)
    exact IsDiscreteValuationRing.not_a_field (T.presheaf.stalk η)
      (congrArg PrimeSpectrum.asIdeal h3).symm
  have hξt : t.base ξ ≠ IsLocalRing.closedPoint R := fun h => hξne (hgen ξ hξη h)

  have hcomp : ∀ Z ∈ irreducibleComponents T, η ∈ Z → Z = closure {ξ} := by
    intro Z hZ hηZ
    have hZirr : IsIrreducible Z := hZ.1
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hz : IsGenericPoint hZirr.genericPoint Z := hZirr.isGenericPoint_genericPoint hZcl
    have hzmem : hZirr.genericPoint ∈ Set.range (T.fromSpecStalk η).base := by
      rw [Scheme.range_fromSpecStalk]; exact hz.specializes hηZ
    obtain ⟨q, hq⟩ := hzmem
    have hξz : ξ ⤳ hZirr.genericPoint := by
      rw [← hq]
      refine Specializes.map ?_ (T.fromSpecStalk η).base.hom.continuous
      exact (PrimeSpectrum.le_iff_specializes _ q).mp (show (⊥ : Ideal (T.presheaf.stalk η)) ≤ q.asIdeal from bot_le)
    have h1 : Z ⊆ closure {ξ} := by
      rw [← hz.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξz))
        isClosed_closure
    exact h1.antisymm (hZ.2 isIrreducible_singleton.closure h1)

  have hZ₀ : irreducibleComponent η ∈ irreducibleComponents T :=
    irreducibleComponent_mem_irreducibleComponents η
  have hZ₀eq : irreducibleComponent η = closure {ξ} := hcomp _ hZ₀ mem_irreducibleComponent
  let U₀ : T.Opens := T.irreducibleComponentOpen (irreducibleComponent η)
  have hηU₀ : η ∈ U₀ := by
    show η ∈ (⋃₀ (irreducibleComponents T \ {irreducibleComponent η}))ᶜ
    rintro ⟨Z, ⟨hZ, hZne⟩, hηZ⟩
    exact hZne ((hcomp Z hZ hηZ).trans hZ₀eq.symm)
  have hξU₀ : ξ ∈ U₀ := hξη.mem_open U₀.2 hηU₀
  have hU₀Z₀ : (U₀ : Set T) ⊆ irreducibleComponent η := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (irreducibleComponent η) hZ₀]
    exact subset_closure
  have hU₀irr : IsIrreducible (U₀ : Set T) :=
    ⟨⟨η, hηU₀⟩, hZ₀.1.2.open_subset U₀.2 hU₀Z₀⟩
  haveI : IrreducibleSpace U₀.toScheme := Subtype.irreducibleSpace hU₀irr
  haveI : IsIntegral U₀.toScheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨‹_›, inferInstance⟩

  haveI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hY : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1

  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  have hmemUgen : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ Ugen := by
    intro x hx
    change x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    change t.base x ∈ (specGenericFibreInclusion R K).opensRange
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    apply PrimeSpectrum.ext
    have h1 : ((specGenericFibreInclusion R K).base (IsLocalRing.closedPoint K)).asIdeal = ⊥ := by
      change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot (R := K), Ideal.comap_bot_of_injective _
        (IsFractionRing.injective R K)]
    have h2 : (t.base x).asIdeal = ⊥ := by
      by_contra hne
      apply hx
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (t.base x).isPrime)
    rw [h1, h2]
  let D : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ Ugen
  have hξD : (⟨ξ, hξU₀⟩ : U₀.toScheme) ∈ D := by
    show U₀.ι.base ⟨ξ, hξU₀⟩ ∈ Ugen
    exact hmemUgen ξ hξt
  have hDdense : Dense (D : Set U₀.toScheme) := D.2.dense ⟨⟨ξ, hξU₀⟩, hξD⟩
  have hDrange : Set.range (D.ι ≫ U₀.ι).base ⊆
      Set.range (pullback.fst t (specGenericFibreInclusion R K)).base := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange]
    exact z.2
  let f₀ : U₀.toScheme.PartialMap X :=
    { domain := D
      dense_domain := hDdense
      hom := IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫ U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K) }
  have hf₀ : f₀.hom ≫ f = f₀.domain.ι ≫ (U₀.ι ≫ t) := by
    show (IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫ U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) ≫ f = D.ι ≫ U₀.ι ≫ t
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% uK.2, ← pullback.condition, IsOpenImmersion.lift_fac_assoc,
      Category.assoc]

  let η' : U₀.toScheme := ⟨η, hηU₀⟩
  have hιη : U₀.ι.base η' = η := rfl
  have hsmU : Smooth (U₀.ι ≫ t) := MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance
  have hη's : (U₀.ι ≫ t).base η' = IsLocalRing.closedPoint R := by
    show t.base (U₀.ι.base η') = _
    rw [hιη, hηs]
  have hgen' : ∀ y : U₀.toScheme, y ⤳ η' → (U₀.ι ≫ t).base y = IsLocalRing.closedPoint R → y = η' := by
    intro y hy hys
    apply U₀.ι.isOpenEmbedding.injective
    rw [hιη]
    apply hgen
    · rw [← hιη]; exact hy.map U₀.ι.base.hom.continuous
    · exact hys
  obtain ⟨hd', hdvr'⟩ := @AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    R _ _ _ _ (U₀.ι ≫ t) hsmU η' hη's hgen'
  have hx : ValuationRing (U₀.toScheme.presheaf.stalk η') := inferInstance
  have hmem : η' ∈ f₀.toRationalMap.domain :=
    AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
      (U₀.ι ≫ t) f hY f₀ hf₀ η' hx

  let g₀ : U₀.toScheme.PartialMap X := f₀.toRationalMap.toPartialMap
  have hle : D ≤ g₀.domain := f₀.le_domain_toRationalMap
  have hres : U₀.toScheme.homOfLE hle ≫ g₀.hom = f₀.hom := by
    have h := f₀.toPartialMap_toRationalMap_restrict
    rw [Scheme.PartialMap.restrict_hom] at h
    exact h
  haveI : IsDominant (U₀.toScheme.homOfLE hle) := AlgebraicGeometry.Opens.isDominant_homOfLE hDdense hle
  have hg₀ : g₀.hom ≫ f = g₀.domain.ι ≫ U₀.ι ≫ t := by
    apply ext_of_isDominant (U₀.toScheme.homOfLE hle)
    rw [reassoc_of% hres, hf₀, Scheme.homOfLE_ι_assoc]

  let U : T.Opens := U₀.ι ''ᵁ g₀.domain
  have hηU : η ∈ U := ⟨η', hmem, rfl⟩
  have hgU : ((U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, hg₀, Scheme.Hom.isoImage_inv_ι_assoc]
  refine ⟨U, hηU, ⟨(U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom, hgU⟩, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]

    have hθrange : Set.range (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι).base ⊆
        Set.range (D.ι ≫ U₀.ι).base := by
      rintro _ ⟨z, rfl⟩
      have hz : (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈
          (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).opensRange := ⟨z, rfl⟩
      rw [Scheme.Hom.opensRange_pullbackFst] at hz
      obtain ⟨x, hx, hxe⟩ := ((pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z).2
      have hxD : x ∈ D := by
        change U₀.ι.base x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact (congrArg (fun y : T => y ∈ t ⁻¹ᵁ (specGenericFibreInclusion R K).opensRange) hxe).mpr hz
      exact ⟨⟨x, hxD⟩, hxe⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : pullback (U.ι ≫ t) (specGenericFibreInclusion R K) ⟶ D.toScheme,
        θ ≫ D.ι ≫ U₀.ι = pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι :=
      ⟨IsOpenImmersion.lift (D.ι ≫ U₀.ι) _ hθrange, IsOpenImmersion.lift_fac _ _ _⟩
    have hA : pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ (U₀.ι.isoImage g₀.domain).inv =
        θ ≫ U₀.toScheme.homOfLE hle := by
      rw [← cancel_mono (g₀.domain.ι ≫ U₀.ι), Category.assoc, Scheme.Hom.isoImage_inv_ι,
        Category.assoc, Scheme.homOfLE_ι_assoc, hθ]
    rw [reassoc_of% hA, hres]
    show θ ≫ (IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫ U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) =
      pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)
    rw [← Category.assoc θ]
    congr 1
    rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K)), Category.assoc,
      IsOpenImmersion.lift_fac, hθ]
    simp only [pullback.map, pullback.lift_fst]
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
    rw [uK.2, pullback.lift_snd, Category.comp_id]

end S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth (solution)
