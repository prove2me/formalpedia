-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/525696ea-6ffd-5306-a960-05dd0c28f3ec

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace WNMP

theorem isOpenImmersion_specMap_fractionRing (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ) (nonZeroDivisors R) ?_ ?_).mpr
      (inferInstance : IsFractionRing R K)
    · exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    · intro n hn
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hn) hϖ
      exact ⟨ϖ ^ k, ⟨k, rfl⟩, ⟨u, hu.symm⟩⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem isDominant_of_genericPoint_mem {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : genericPoint Y ∈ Set.range f.base) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have hc : closure ({genericPoint Y} : Set Y) = (⊤ : Set Y) := genericPoint_spec Y
  rw [Set.top_eq_univ] at hc
  rw [← hc]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

end WNMP

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} [IsSeparated gK]
    (M : ModelFamily R K gK) (hM : ∀ i, LocallyOfFiniteType (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ) :
    ∃ (i : M.ι) (U : Z.Opens) (_ : ζ ∈ U) (u : SchemeHomOver (U.ι ≫ z) (M.str i)),
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K (M.str i) (U.ι ≫ z) u) (M.chart i)).1 =
        pullback.map (U.ι ≫ z) (specGenericFibreInclusion R K) z (specGenericFibreInclusion R K) U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical

  let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial
  let φc : CommRingCat.of R ⟶ Z.presheaf.stalk ζ := g ≫ z.stalkMap ζ
  letI algRO : Algebra R (Z.presheaf.stalk ζ) := φc.hom.toAlgebra
  have hfac : Z.fromSpecStalk ζ ≫ z = Spec.map φc := by
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk z, Spec.fromSpecStalk_eq]
  have halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))) := by
    rw [hfac]; rfl
  obtain ⟨hdom, hdvr, hloc, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes z ζ hζ hmax halg
  haveI := hdom
  haveI := hdvr
  haveI := hloc

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have hne0 : algebraMap R (Z.presheaf.stalk ζ) ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Z.presheaf.stalk ζ)
    rw [← hidx.map_maximalIdeal, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton, h0, Ideal.span_singleton_eq_bot]
  have hinj : Function.Injective (algebraMap R (Z.presheaf.stalk ζ)) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    haveI : (RingHom.ker (algebraMap R (Z.presheaf.stalk ζ))).IsPrime := RingHom.ker_isPrime _
    have hmax' := Ring.DimensionLEOne.maximalOfPrime hker this
    have : ϖ ∈ RingHom.ker (algebraMap R (Z.presheaf.stalk ζ)) := by
      rw [IsLocalRing.eq_maximalIdeal hmax']; exact hϖm
    exact hne0 this
  have hinjK : Function.Injective (algebraMap R (FractionRing (Z.presheaf.stalk ζ))) := by
    rw [IsScalarTower.algebraMap_eq R (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ))]
    exact (IsFractionRing.injective (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ))).comp hinj
  letI algKK : Algebra K (FractionRing (Z.presheaf.stalk ζ)) := (IsFractionRing.lift hinjK).toAlgebra
  haveI : IsScalarTower R K (FractionRing (Z.presheaf.stalk ζ)) :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hinjK r).symm

  let xZ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) z := ⟨Z.fromSpecStalk ζ, halg⟩
  obtain ⟨i, x, hx⟩ := hpts (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ)) hidx
    (schemeHomOverComp (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ) uK)

  haveI := hM i
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  obtain ⟨U, hζU, v, hv, hvx⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk z (M.str i) ζ x.1 (x.2.trans halg.symm)

  have hstalk : ∀ y : Z, IsDomain (Z.presheaf.stalk y) := fun y =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R z y).1
  haveI : IsReduced Z := by
    haveI : ∀ y : Z, _root_.IsReduced (Z.presheaf.stalk y) := fun y => by haveI := hstalk y; infer_instance
    exact isReduced_of_isReduced_stalk Z
  obtain ⟨hCopen, -⟩ := AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hstalk ζ
  let C : Z.Opens := ⟨irreducibleComponent ζ, hCopen⟩
  let U' : Z.Opens := U ⊓ C
  have hζU' : ζ ∈ U' := ⟨hζU, mem_irreducibleComponent⟩
  haveI hqs : QuasiSober (U' : Set Z) := U'.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  haveI hirr : IrreducibleSpace (U' : Set Z) := by
    refine Subtype.irreducibleSpace ⟨⟨ζ, hζU'⟩, ?_⟩
    exact isIrreducible_irreducibleComponent.isPreirreducible.open_subset U'.isOpen (fun y hy => hy.2)
  haveI hqs' : QuasiSober (U' : Scheme.{u}) := hqs
  haveI hirr' : IrreducibleSpace (U' : Scheme.{u}) := hirr

  let v' : (U' : Scheme.{u}) ⟶ M.X i := Z.homOfLE inf_le_left ≫ v
  have hv' : v' ≫ M.str i = U'.ι ≫ z := by
    rw [Category.assoc, hv, ← Category.assoc, Scheme.homOfLE_ι]
  have hvx' : U'.fromSpecStalkOfMem ζ hζU' ≫ v' = x.1 := by
    rw [← hvx, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨i, U', hζU', ⟨v', hv'⟩, ?_⟩

  haveI : IsOpenImmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]; exact WNMP.isOpenImmersion_specMap_fractionRing R K
  haveI : IsReduced (U' : Scheme.{u}) := isReduced_of_isOpenImmersion U'.ι
  haveI : IsReduced (pullback (U'.ι ≫ z) (specGenericFibreInclusion R K)) :=
    isReduced_of_isOpenImmersion (pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K))

  let xU : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) (U'.ι ≫ z) :=
    ⟨U'.fromSpecStalkOfMem ζ hζU', by rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]; exact halg⟩
  let ιK := (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xU).1

  haveI hdomO : IsDominant (U'.fromSpecStalkOfMem ζ hζU') := by
    apply WNMP.isDominant_of_genericPoint_mem
    have hsp : (U'.ι).base (genericPoint (U' : Scheme.{u})) ⤳ ζ :=
      (genericPoint_specializes (⟨ζ, hζU'⟩ : (U' : Scheme.{u}))).map U'.ι.base.hom.continuous
    have hmem : (U'.ι).base (genericPoint (U' : Scheme.{u})) ∈ Set.range (Z.fromSpecStalk ζ).base := by
      rw [Scheme.range_fromSpecStalk]; exact hsp
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, ?_⟩
    apply U'.ι.isOpenEmbedding.injective
    rw [← hq, ← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι]
  haveI hdomK : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ))))) := by
    apply WNMP.isDominant_of_genericPoint_mem
    refine ⟨IsLocalRing.closedPoint _, ?_⟩
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ)))
      (IsLocalRing.maximalIdeal (FractionRing (Z.presheaf.stalk ζ))) = ⊥
    have hm : IsLocalRing.maximalIdeal (FractionRing (Z.presheaf.stalk ζ)) = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [hm, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (Z.presheaf.stalk ζ) _)]
  haveI : IsDominant ιK := by
    have hcomp : ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) =
        Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ)))) ≫
          U'.fromSpecStalkOfMem ζ hζU' :=
      pointGenericFibre_coe_comp_fst xU
    haveI : IsDominant (ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K)) := by
      rw [hcomp]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion ιK (pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K))

  have hxval : (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) x).1 ≫ (M.chart i).1 =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ).1 ≫ uK.1 :=
    congrArg Subtype.val hx
  have hleft : ιK ≫ (genericFibreRestrict R K (M.str i) (U'.ι ≫ z) ⟨v', hv'⟩).1 =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) x).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show ιK ≫ (genericFibreRestrict R K (M.str i) (U'.ι ≫ z) ⟨v', hv'⟩).1 ≫ pullback.fst _ _ = _
      simp only [genericFibreRestrict, pullback.lift_fst]
      rw [← Category.assoc, show ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from
        pointGenericFibre_coe_comp_fst xU, pointGenericFibre_coe_comp_fst x, Category.assoc, hvx']
    · rw [Category.assoc]
      simp only [genericFibreRestrict, pullback.lift_snd]
      rw [show ιK ≫ pullback.snd (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from
        pointGenericFibre_coe_comp_snd xU, pointGenericFibre_coe_comp_snd x]
  have hright : ιK ≫ pullback.map (U'.ι ≫ z) (specGenericFibreInclusion R K) z (specGenericFibreInclusion R K) U'.ι
      (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        show ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from pointGenericFibre_coe_comp_fst xU,
        pointGenericFibre_coe_comp_fst xZ, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        show ιK ≫ pullback.snd (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from pointGenericFibre_coe_comp_snd xU,
        pointGenericFibre_coe_comp_snd xZ, Category.comp_id]
  apply ext_of_isDominant_of_isSeparated gK ?_ ιK ?_
  ·
    rw [(schemeHomOverComp (genericFibreRestrict R K (M.str i) (U'.ι ≫ z) ⟨v', hv'⟩) (M.chart i)).2,
      Category.assoc, uK.2, pullback.lift_snd, Category.comp_id]
  · rw [schemeHomOverComp_coe, ← Category.assoc, hleft, hxval, ← Category.assoc, hright]

end S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints (solution)
