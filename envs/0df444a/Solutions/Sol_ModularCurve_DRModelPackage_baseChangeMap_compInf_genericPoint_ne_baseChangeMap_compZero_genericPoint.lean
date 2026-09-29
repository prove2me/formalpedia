-- Prove2me | solution 1 for ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/27a54448-f65f-5a67-b57d-8f226dad4cff

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint.ModularCurve AlgebraicCurve IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRModel.baseChangeMap DRModel.not_irreducibleSpace_pullback_toBase_of_charP"
namespace Distinct
p2m_open "ModularCurve"

section

variable (p : ℕ) [hp : Fact p.Prime]

abbrev XR (R : Type) [CommRing R] : Scheme := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))

variable {p}

section MapLemmas
universe v u
variable {C : Type u} [Category.{v} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂)

@[reassoc]
theorem map_fst' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

end MapLemmas

theorem baseChangeMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    (DRModel.baseChangeMap (p := p) (g.comp f)) = DRModel.baseChangeMap g ≫ DRModel.baseChangeMap f := by
  apply pullback.hom_ext
  · unfold DRModel.baseChangeMap
    simp only [Category.assoc, map_fst', map_fst'_assoc, Category.comp_id]
  · unfold DRModel.baseChangeMap
    simp only [Category.assoc, map_snd', map_snd'_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem baseChangeMap_injective_of_surjective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : Function.Injective (DRModel.baseChangeMap (p := p) f).base := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom f)) := IsClosedImmersion.spec_of_surjective _ hf
  haveI : IsClosedImmersion (DRModel.baseChangeMap (p := p) f) := by
    unfold DRModel.baseChangeMap
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) (i₁ := 𝟙 (DRModel p))
      (i₂ := Spec.map (CommRingCat.ofHom f)) inferInstance inferInstance (by rw [Category.id_comp])
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _)
  exact (DRModel.baseChangeMap (p := p) f).isClosedEmbedding.injective

theorem baseChangeMap_surjective_of_field {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Function.Surjective (DRModel.baseChangeMap (p := p) f).base := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom f)) :=
    ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Surjective (DRModel.baseChangeMap (p := p) f) := by
    unfold DRModel.baseChangeMap
    exact MorphismProperty.pullbackMap (P := @Surjective) (i₁ := 𝟙 (DRModel p))
      (i₂ := Spec.map (CommRingCat.ofHom f)) inferInstance inferInstance (by rw [Category.id_comp])
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _)
  exact (DRModel.baseChangeMap (p := p) f).surjective

variable (p)

theorem genericPoint_ne (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsLocalRing O] (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C) ≠
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C) := by

  have hker : RingHom.ker toκ = maximalIdeal O := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ)
    · rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast,
        CharP.cast_eq_zero]
  let ι₀ : ResidueField O →+* κ := Ideal.Quotient.lift (maximalIdeal O) toκ
    (fun a ha => by rwa [← hker, RingHom.mem_ker] at ha)
  have hι₀ : ι₀.comp (residue O) = toκ := RingHom.ext fun _ => rfl
  haveI : CharP (ResidueField O) p := by
    refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
    rw [← map_natCast (residue O), IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.subset_span rfl

  have hfac : DRModel.baseChangeMap (p := p) toκ =
      DRModel.baseChangeMap ι₀ ≫ DRModel.baseChangeMap (residue O) := by
    rw [← baseChangeMap_comp, hι₀]
  intro h

  have h' : (𝔛.compInf κ ≫ DRModel.baseChangeMap ι₀).base (genericPoint (𝔛.ratModel κ).C) =
      (𝔛.compZero κ ≫ DRModel.baseChangeMap ι₀).base (genericPoint (𝔛.ratModel κ).C) := by
    apply baseChangeMap_injective_of_surjective (p := p) (residue O) Ideal.Quotient.mk_surjective
    have h2 := h
    rw [hfac] at h2
    simpa [Scheme.Hom.comp_base] using h2

  have hgen : ∀ m : ↥(𝔛.ratModel κ).C, genericPoint (𝔛.ratModel κ).C ⤳ m := fun m =>
    (genericPoint_spec (𝔛.ratModel κ).C).specializes (Set.mem_univ m)
  have hspec : ∀ y : ↥(XR p (ResidueField O)),
      (𝔛.compInf κ ≫ DRModel.baseChangeMap ι₀).base (genericPoint (𝔛.ratModel κ).C) ⤳ y := by
    intro y
    obtain ⟨z, rfl⟩ := baseChangeMap_surjective_of_field (p := p) ι₀ y
    rcases 𝔛.comp_jointly_surjective κ z with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have := (hgen m).map (𝔛.compInf κ ≫ DRModel.baseChangeMap ι₀).base.hom.continuous
      simpa [Scheme.Hom.comp_base] using this
    · have := (hgen m).map (𝔛.compZero κ ≫ DRModel.baseChangeMap ι₀).base.hom.continuous
      rw [h']
      simpa [Scheme.Hom.comp_base] using this

  apply ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP p (ResidueField O)
  have hcl : closure ({(𝔛.compInf κ ≫ DRModel.baseChangeMap ι₀).base (genericPoint (𝔛.ratModel κ).C)} :
      Set ↥(XR p (ResidueField O))) = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.mp (hspec y)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  exact { isPreirreducible_univ := by rw [← hcl]; exact isIrreducible_singleton.isPreirreducible.closure
          toNonempty := ⟨(𝔛.compInf κ ≫ DRModel.baseChangeMap ι₀).base (genericPoint (𝔛.ratModel κ).C)⟩ }

end

end ModularCurve.Distinct

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint.ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsLocalRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C) ≠
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C) :=
  ModularCurve.Distinct.genericPoint_ne p 𝔛 O hϖ κ toκ

end S_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint (solution)
