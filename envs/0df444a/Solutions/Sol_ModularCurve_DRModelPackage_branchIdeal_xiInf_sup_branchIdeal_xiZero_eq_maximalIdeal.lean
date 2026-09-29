-- Prove2me | solution 1 for ModularCurve.DRModelPackage.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2219800d-470d-5336-a0c9-ac361a7544cd

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

section Unit1

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopCat

universe u

namespace TransvPlumb2

private theorem flat_pullbackMap {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (i : T' ⟶ T)
    [Flat i] (e : i ≫ g = g') (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 S = i ≫ g) :
    Flat (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂) := by
  subst e
  have hm : pullback.map f (i ≫ g) f g (𝟙 X) i (𝟙 S) e₁ e₂ =
      (pullbackLeftPullbackSndIso f g i).inv ≫ pullback.fst (pullback.snd f g) i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.condition, pullbackLeftPullbackSndIso_inv_snd_snd_assoc]
  rw [hm]
  infer_instance

end TransvPlumb2

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal.ModularCurve ModularCurve.DRModelPackage P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal.ModularCurve.DRModelPackage IsLocalRing"

namespace TransvL1

private theorem isClosedImmersion_pullbackMap {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S)
    (i : T' ⟶ T) [IsClosedImmersion i] (e : i ≫ g = g') (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 S = i ≫ g) :
    IsClosedImmersion (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂) := by
  subst e
  have hm : pullback.map f (i ≫ g) f g (𝟙 X) i (𝟙 S) e₁ e₂ =
      (pullbackLeftPullbackSndIso f g i).inv ≫ pullback.fst (pullback.snd f g) i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.condition, pullbackLeftPullbackSndIso_inv_snd_snd_assoc]
  rw [hm]
  infer_instance

variable {p : ℕ} [Fact p.Prime]

private theorem specMap_comp_specMap_algebraMap_int {O O' : Type} [CommRing O] [CommRing O'] (φ : O →+* O') :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ O')) := by
  rw [← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext_int _ _

section residue

variable (O : Type) [CommRing O] [IsLocalRing O] (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] (toκ : O →+* κ)
include hϖ

omit [Fact p.Prime] in

private theorem isLocalHom_of_charP : IsLocalHom toκ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal O := (mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hna)
  rw [hϖ, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, rfl⟩ := hmem
  rw [map_mul, map_natCast, CharP.cast_eq_zero, mul_zero] at ha
  exact not_isUnit_zero ha

private noncomputable def resLift : ResidueField O →+* κ :=
  haveI := isLocalHom_of_charP O hϖ κ toκ
  ResidueField.lift toκ

omit [Fact p.Prime] in
private theorem resLift_comp_residue : (resLift O hϖ κ toκ).comp (residue O) = toκ := by
  haveI := isLocalHom_of_charP O hϖ κ toκ
  exact ResidueField.lift_comp_residue toκ

private theorem baseChangeMap_resLift_comp :
    DRModel.baseChangeMap (p := p) (resLift O hϖ κ toκ) ≫ DRModel.baseChangeMap (residue O) =
      DRModel.baseChangeMap toκ := by
  unfold DRModel.baseChangeMap
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resLift_comp_residue]

private theorem flat_baseChangeMap_resLift : Flat (DRModel.baseChangeMap (p := p) (resLift O hϖ κ toκ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (resLift O hϖ κ toκ))) := by
    rw [Flat.SpecMap_iff]
    change (resLift O hϖ κ toκ).Flat
    letI := (resLift O hϖ κ toκ).toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  unfold DRModel.baseChangeMap
  exact TransvPlumb2.flat_pullbackMap _ _ _ _ (specMap_comp_specMap_algebraMap_int _) _ _

private theorem flat_stalkMap_baseChangeMap_resLift (y : ↥(baseChangeO p κ)) :
    ((DRModel.baseChangeMap (p := p) (resLift O hϖ κ toκ)).stalkMap y).hom.Flat :=
  haveI := flat_baseChangeMap_resLift (p := p) O hϖ κ toκ
  Flat.stalkMap _ y

omit hϖ in

private theorem isClosedImmersion_baseChangeMap_residue :
    IsClosedImmersion (DRModel.baseChangeMap (p := p) (residue O)) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold DRModel.baseChangeMap
  exact TransvL1.isClosedImmersion_pullbackMap _ _ _ _ (specMap_comp_specMap_algebraMap_int _) _ _

omit hϖ in

private theorem stalkMap_baseChangeMap_residue_surjective (x : ↥(baseChangeO p (ResidueField O))) :
    Function.Surjective ((DRModel.baseChangeMap (p := p) (residue O)).stalkMap x) :=
  haveI := isClosedImmersion_baseChangeMap_residue (p := p) O
  (DRModel.baseChangeMap (p := p) (residue O)).stalkMap_surjective x

private theorem stalkMap_baseChangeMap_eq (y : ↥(baseChangeO p κ)) :
    (DRModel.baseChangeMap (p := p) toκ).stalkMap y =
      ((baseChangeO p O).presheaf.stalkCongr
          (.of_eq (by rw [← Scheme.Hom.comp_apply, baseChangeMap_resLift_comp (p := p) O hϖ κ toκ]))).hom ≫
        (DRModel.baseChangeMap (p := p) (residue O)).stalkMap
            ((DRModel.baseChangeMap (p := p) (resLift O hϖ κ toκ)).base y) ≫
          (DRModel.baseChangeMap (p := p) (resLift O hϖ κ toκ)).stalkMap y := by
  rw [Scheme.Hom.stalkMap_congr_hom _ _ (baseChangeMap_resLift_comp (p := p) O hϖ κ toκ).symm y,
    Scheme.Hom.stalkMap_comp]
  rfl

end residue

section crossing

variable (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

end crossing

end TransvL1

end Unit1

section Unit2

set_option autoImplicit false

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage DRModel.isReduced_pullback_toBase_of_charP"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "baseChangeO crossingPt ξinf ξzero smoothLocus comp_jointly_surjective compInf_isClosedImmersion flat compZero_isClosedImmersion compZero ratModel compInf crossing_reduced mk baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero baseChangeMap_genericPoint_mem_preimage_smoothLocus"
p2m_open "ModularCurve.DRModelPackage ModularCurve"

private theorem fromSpecStalk_comap_closedPoint_spec {X : Scheme} {x ξ : X} (h : ξ ⤳ x) :
    X.fromSpecStalk x (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom (closedPoint (X.presheaf.stalk ξ))) =
      ξ := by
  have e := congrArg (fun f : Spec (X.presheaf.stalk ξ) ⟶ X => f (closedPoint (X.presheaf.stalk ξ)))
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, Scheme.fromSpecStalk_closedPoint] using e

private theorem exists_specializes_and_eq_comap_stalkSpecializes {X : Scheme} (y : X)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    ∃ (z : X) (hz : z ⤳ y),
      𝔮 = Ideal.comap (X.presheaf.stalkSpecializes hz).hom (maximalIdeal (X.presheaf.stalk z)) := by
  let q : Spec (X.presheaf.stalk y) := ⟨𝔮, inferInstance⟩
  have hz : X.fromSpecStalk y q ⤳ y := by
    have hmem : X.fromSpecStalk y q ∈ Set.range (X.fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  refine ⟨X.fromSpecStalk y q, hz, ?_⟩
  have hinj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  have h1 := hinj (fromSpecStalk_comap_closedPoint_spec hz)
  exact (congrArg PrimeSpectrum.asIdeal h1).symm

private theorem comap_stalkSpecializes_refl_maximalIdeal {X : Scheme} (y : X) :
    Ideal.comap (X.presheaf.stalkSpecializes (specializes_refl y)).hom (maximalIdeal (X.presheaf.stalk y)) =
      maximalIdeal (X.presheaf.stalk y) := by
  simp

private theorem eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hsurj : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂ := by
  obtain ⟨z, hz, rfl⟩ := exists_specializes_and_eq_comap_stalkSpecializes y 𝔮
  rcases hsurj z with ⟨c, hc⟩ | ⟨c, hc⟩
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inl rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inr rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)

private theorem eq_of_branchIdeal_eq {X : Scheme} {x ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ x) (h₂ : ξ₂ ⤳ x)
    (h : Scheme.branchIdeal h₁ = Scheme.branchIdeal h₂) : ξ₁ = ξ₂ := by
  have hpt : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) =
      PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    PrimeSpectrum.ext h
  rw [← fromSpecStalk_comap_closedPoint_spec h₁, ← fromSpecStalk_comap_closedPoint_spec h₂, hpt]

private theorem specializes_of_branchIdeal_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (hle : Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂) : ξ₁ ⤳ ξ₂ := by
  have hsp : (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) :
      Spec (X.presheaf.stalk y)) ⤳
        PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have := hsp.map (X.fromSpecStalk y).continuous
  rwa [fromSpecStalk_comap_closedPoint_spec h₁, fromSpecStalk_comap_closedPoint_spec h₂] at this

private theorem branchIdeal_ne_maximalIdeal_and_not_le {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (hne : i₁.base η ≠ i₂.base η) (hy₁ : i₁.base η ≠ y) (hy₂ : i₂.base η ≠ y) :
    Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      Scheme.branchIdeal h₂ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      ¬ Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂ ∧ ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁ := by
  refine ⟨fun h => hy₁ ?_, fun h => hy₂ ?_, fun hle => ?_, fun hle => ?_⟩
  · exact eq_of_branchIdeal_eq h₁ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  · exact eq_of_branchIdeal_eq h₂ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  ·

    have hsp := specializes_of_branchIdeal_le h₁ h₂ hle
    obtain ⟨c, hc⟩ : i₂.base η ∈ Set.range i₁.base :=
      hsp.mem_closed i₁.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₂.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₂ (h₂.mem_closed hcl (Set.mem_singleton _)).symm
  · have hsp := specializes_of_branchIdeal_le h₂ h₁ hle
    obtain ⟨c, hc⟩ : i₁.base η ∈ Set.range i₂.base :=
      hsp.mem_closed i₂.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₁.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₁ (h₁.mem_closed hcl (Set.mem_singleton _)).symm

private theorem eq_branchIdeal_of_isPrime_of_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (htri : ∀ 𝔮 : Ideal (X.presheaf.stalk y), 𝔮.IsPrime →
      𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂)
    (hP : Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y))
    (hQP : ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁)
    (J : Ideal (X.presheaf.stalk y)) [hJp : J.IsPrime] (hJ : J ≤ Scheme.branchIdeal h₁) :
    J = Scheme.branchIdeal h₁ := by
  rcases htri J hJp with hm | hp | hq
  · subst hm
    exact absurd (le_antisymm (le_maximalIdeal (Scheme.branchIdeal_isPrime h₁).ne_top) hJ) hP
  · exact hp
  · subst hq
    exact absurd hJ hQP

section Frame

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

private theorem compInf_genericPoint_specializes (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C) ⤳
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) :=
  (genericPoint_specializes _).map (𝔛.compInf κ).continuous

private theorem compZero_snd_eq_compInf_fst (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compZero κ).base ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n) =
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) := by
  have h := congrArg (fun f : pullback (𝔛.compInf κ) (𝔛.compZero κ) ⟶ _ => f.base n)
    (pullback.condition (f := 𝔛.compInf κ) (g := 𝔛.compZero κ))
  simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h.symm

private theorem compZero_genericPoint_specializes (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C) ⤳
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) :=
  ((genericPoint_specializes _).map (𝔛.compZero κ).continuous).trans
    (specializes_of_eq (compZero_snd_eq_compInf_fst p 𝔛 κ n))

private theorem frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (𝔮 : Ideal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.stalk
      ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)))) [𝔮.IsPrime] :
    𝔮 = maximalIdeal _ ∨ 𝔮 = Scheme.branchIdeal (compInf_genericPoint_specializes p 𝔛 κ n) ∨
      𝔮 = Scheme.branchIdeal (compZero_genericPoint_specializes p 𝔛 κ n) :=
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal (𝔛.compInf κ) (𝔛.compZero κ) (𝔛.comp_jointly_surjective κ)
    (genericPoint (𝔛.ratModel κ).C)
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.ratModel κ).toBase c hc)
    (compInf_genericPoint_specializes p 𝔛 κ n) (compZero_genericPoint_specializes p 𝔛 κ n) 𝔮

private theorem frame_branchIdeal_ne_maximalIdeal_and_not_le
    (O : Type) [CommRing O] [IsLocalRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* κ) (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hy₁ : (𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C) ≠
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))
    (hy₂ : (𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C) ≠
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)) :
    Scheme.branchIdeal (compInf_genericPoint_specializes p 𝔛 κ n) ≠ maximalIdeal _ ∧
      Scheme.branchIdeal (compZero_genericPoint_specializes p 𝔛 κ n) ≠ maximalIdeal _ ∧
      ¬ Scheme.branchIdeal (compInf_genericPoint_specializes p 𝔛 κ n) ≤
          Scheme.branchIdeal (compZero_genericPoint_specializes p 𝔛 κ n) ∧
      ¬ Scheme.branchIdeal (compZero_genericPoint_specializes p 𝔛 κ n) ≤
          Scheme.branchIdeal (compInf_genericPoint_specializes p 𝔛 κ n) :=
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  have hne : (𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C) ≠
      (𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C) := fun h =>
    baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint p 𝔛 O hϖ κ toκ
      (by simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using congrArg (DRModel.baseChangeMap toκ).base h)
  branchIdeal_ne_maximalIdeal_and_not_le (𝔛.compInf κ) (𝔛.compZero κ) (genericPoint (𝔛.ratModel κ).C)
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.ratModel κ).toBase c hc)
    (compInf_genericPoint_specializes p 𝔛 κ n) (compZero_genericPoint_specializes p 𝔛 κ n) hne hy₁ hy₂

omit [CharP κ p] [IsAlgClosed κ] in

private theorem baseChangeMap_comp_fst (O : Type) [CommRing O] (toκ : O →+* κ) :
    DRModel.baseChangeMap toκ ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) := by
  rw [DRModel.baseChangeMap]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem compInf_genericPoint_ne_and_compZero_genericPoint_ne (O : Type) [CommRing O] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C) ≠
        (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) ∧
      (𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C) ≠
        (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) := by
  have hy : (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) ∈ Set.range (𝔛.compInf κ).base ∧
      (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) ∈ Set.range (𝔛.compZero κ).base :=
    ⟨⟨_, rfl⟩, ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, compZero_snd_eq_compInf_fst p 𝔛 κ n⟩⟩
  have hsm := baseChangeMap_genericPoint_mem_preimage_smoothLocus p 𝔛 O κ toκ
  have key : ∀ z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      (DRModel.baseChangeMap toκ).base z ∈
          (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) →
        z ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    intro z hz
    rw [Scheme.Hom.mem_preimage] at hz ⊢
    rw [← baseChangeMap_comp_fst p κ O toκ, Scheme.Hom.comp_base, TopCat.comp_app]
    exact hz
  have h1 := key _ (by simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using hsm.1)
  have h2 := key _ (by simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using hsm.2)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mp h1
      (by rw [h]; exact hy)
  · exact (mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mp h2
      (by rw [h]; exact hy)

end Frame

end ModularCurve.DRModelPackage

end Unit2

section Unit3

set_option autoImplicit false

open TensorProduct

private theorem eq_bot_of_forall_isPrime_le' {T : Type*} [CommRing T] [IsReduced T] {I : Ideal T}
    (h : ∀ 𝔮 : Ideal T, 𝔮.IsPrime → I ≤ 𝔮) : I = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I ≤ sInf { J : Ideal T | J.IsPrime } := le_sInf fun 𝔮 h𝔮 => h 𝔮 h𝔮
    _ = nilradical T := (nilradical_eq_sInf T).symm
    _ = ⊥ := nilradical_eq_zero T

private theorem flat_quotient_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Ideal A) : Module.Flat (A ⧸ P) (B ⧸ P.map (algebraMap A B)) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P).toLinearEquiv

private theorem isSMulRegular_quotient_map_of_notMem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (P : Ideal A) [P.IsPrime] {a : A} (ha : a ∉ P) :
    IsSMulRegular (B ⧸ P.map (algebraMap A B)) (algebraMap A (B ⧸ P.map (algebraMap A B)) a) := by
  haveI := flat_quotient_map_of_flat (A := A) (B := B) P
  have hreg : IsSMulRegular (A ⧸ P) (Ideal.Quotient.mk P a) :=
    mul_right_injective₀ (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
  have h := hreg.of_flat (S := B ⧸ P.map (algebraMap A B))
  rwa [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

private theorem map_eq_of_flat_of_forall_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B}
    (h1 : P.map (algebraMap A B) ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap (algebraMap A B) ≤ P → 𝔭' ≤ 𝔮) :
    P.map (algebraMap A B) = 𝔭' := by
  refine le_antisymm h1 fun q hq => ?_
  let S : Submonoid B := P.primeCompl.map (algebraMap A B)

  have hbot : 𝔭'.map (algebraMap B (Localization S)) = ⊥ := by
    refine eq_bot_of_forall_isPrime_le' fun 𝔔 h𝔔 => ?_
    obtain ⟨hprime, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S (Localization S) 𝔔).mp h𝔔
    refine Ideal.map_le_iff_le_comap.mpr (h2 _ hprime fun a ha => ?_)
    by_contra ha'
    exact Set.disjoint_left.mp hdisj (Submonoid.mem_map_of_mem (algebraMap A B) (ha' : a ∈ P.primeCompl))
      ha
  have hq0 : algebraMap B (Localization S) q = 0 := by
    have : algebraMap B (Localization S) q ∈ 𝔭'.map (algebraMap B (Localization S)) :=
      Ideal.mem_map_of_mem _ hq
    simpa [hbot] using this
  obtain ⟨⟨s, hs⟩, hsq⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) q).mp hq0
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs

  have hreg := isSMulRegular_quotient_map_of_notMem (B := B) P (ha : a ∉ P)
  have hzero : algebraMap A (B ⧸ P.map (algebraMap A B)) a • Ideal.Quotient.mk _ q =
      algebraMap A (B ⧸ P.map (algebraMap A B)) a • (0 : B ⧸ P.map (algebraMap A B)) := by
    rw [smul_zero, smul_eq_mul, IsScalarTower.algebraMap_apply A B (B ⧸ P.map (algebraMap A B)),
      Ideal.Quotient.algebraMap_eq, ← map_mul]
    simpa using congrArg (Ideal.Quotient.mk (P.map (algebraMap A B))) hsq
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg hzero)

private theorem map_eq_of_flat_of_forall_le_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B} (h1 : P.map ψ ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap ψ ≤ P → 𝔭' ≤ 𝔮) : P.map ψ = 𝔭' := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact map_eq_of_flat_of_forall_le P h1 h2

end Unit3

section Unit4

set_option autoImplicit false

private theorem eq_under_of_le_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.under A) : q = 𝔭'.under A := by
  obtain ⟨𝔮, h𝔮le, h𝔮prime, h𝔮over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := 𝔭'.under A) 𝔭' hle
  rw [hmin 𝔮 h𝔮prime h𝔮le] at h𝔮over
  exact h𝔮over.over

private theorem eq_comap_of_le_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hle : q ≤ 𝔭'.comap ψ) : q = 𝔭'.comap ψ := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact eq_under_of_le_of_flat 𝔭' hmin hle

private theorem not_le_comap_of_ne_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {q : Ideal A} [q.IsPrime]
    (hne : q ≠ 𝔭'.comap ψ) : ¬ q ≤ 𝔭'.comap ψ :=
  fun hle => hne (eq_comap_of_le_of_flat_ringHom ψ hψ 𝔭' hmin hle)

end Unit4

section Unit5

set_option autoImplicit false

private theorem eq_of_isRadical_of_le_of_forall_le {B : Type*} [CommRing B] {I 𝔭 : Ideal B}
    (hI : I.IsRadical) [𝔭.IsPrime] (hle : I ≤ 𝔭)
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → I ≤ 𝔮 → 𝔭 ≤ 𝔮) : I = 𝔭 := by
  refine le_antisymm hle ?_
  rw [← Ideal.radical_eq_iff.mpr hI, Ideal.radical_eq_sInf]
  exact le_sInf fun 𝔮 h𝔮 => hmin 𝔮 h𝔮.2 h𝔮.1

private theorem le_of_map_le_map_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {I J : Ideal A}
    (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) : I ≤ J := by
  calc I = (I.map (algebraMap A B)).comap (algebraMap A B) :=
        (Ideal.comap_map_eq_self_of_faithfullyFlat I).symm
    _ ≤ (J.map (algebraMap A B)).comap (algebraMap A B) := Ideal.comap_mono h
    _ = J := Ideal.comap_map_eq_self_of_faithfullyFlat J

private theorem le_of_map_le_map_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {I J : Ideal A}
    (h : I.map f ≤ J.map f) : I ≤ J := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact le_of_map_le_map_of_faithfullyFlat (A := A) (B := B) h

private theorem sup_eq_maximalIdeal_of_map_maximalIdeal_le {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {P Q : Ideal A}
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)
    (h : (IsLocalRing.maximalIdeal A).map f ≤ (P ⊔ Q).map f) :
    P ⊔ Q = IsLocalRing.maximalIdeal A :=
  le_antisymm (sup_le (IsLocalRing.le_maximalIdeal hP) (IsLocalRing.le_maximalIdeal hQ))
    (le_of_map_le_map_of_flat_of_isLocalHom f hf h)

end Unit5

section Unit6

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace TransvChair

variable {X Y : Scheme.{u}}

private theorem comap_stalkMap_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x) :
    ((maximalIdeal (X.presheaf.stalk ξ)).comap (X.presheaf.stalkSpecializes h).hom).comap
        (f.stalkMap x).hom =
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, ← Scheme.Hom.stalkSpecializes_stalkMap f ξ x h,
    CommRingCat.hom_comp, ← Ideal.comap_comap, maximalIdeal_comap]

private theorem ker_stalkMap_le_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x)
    [Nontrivial (X.presheaf.stalk ξ)] :
    RingHom.ker (f.stalkMap x).hom ≤
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  intro s hs
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map (f.stalkMap ξ).hom
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply f ξ x h, RingHom.mem_ker.mp hs, map_zero] at hu'
  exact not_isUnit_zero hu'

private theorem stalkSpecializes_surjective_of_eq {x x' : X} (e : x' = x) :
    Function.Surjective (X.presheaf.stalkSpecializes (specializes_of_eq e)).hom := by
  subst e
  intro t
  refine ⟨t, ?_⟩
  have : X.presheaf.stalkSpecializes (specializes_of_eq (rfl : x' = x')) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl x'
  rw [this]
  rfl

private theorem isRadical_of_specLift {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ X) (x : X)
    (K : Ideal (X.presheaf.stalk x)) [IsLocalRing ((X.presheaf.stalk x) ⧸ K)]
    [IsLocalHom (Ideal.Quotient.mk K)]
    (g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ Z)
    (hg : g ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
    (hpt : (g ≫ j).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x)
    (hK : K ≤ RingHom.ker ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        j.stalkMap (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K)))).hom) :
    K.IsRadical := by
  have claim : ∀ (f : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X)
      (_ : f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (hfpt : f.base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x) (a : X.presheaf.stalk x),
      (Scheme.stalkClosedPointTo f).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom a) =
        Ideal.Quotient.mk K a := by
    intro f hf hfpt a
    subst hf
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have hqU : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x).base
        (closedPoint ((X.presheaf.stalk x) ⧸ K)) ∈ U := by
      rw [hfpt]
      exact hxU
    have e1 : (X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom
          ((X.presheaf.germ U x hxU).hom s) =
        (X.presheaf.germ U _ hqU).hom s := by
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [e1, ← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
    rfl
  rw [Ideal.isRadical_iff_quotient_reduced]
  refine ⟨fun r ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hb : (Scheme.stalkClosedPointTo g).hom
        ((j.stalkMap (g.base (closedPoint _))).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) =
      Ideal.Quotient.mk K a := by
    have := claim (g ≫ j) hg hpt a
    rw [Scheme.stalkClosedPointTo_comp] at this
    simp only [CommRingCat.comp_apply] at this
    exact this
  have ham : a ^ m ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact hm
  have hbm := hK ham
  rw [RingHom.mem_ker, map_pow, CommRingCat.hom_comp, RingHom.comp_apply] at hbm
  have hb0 := IsReduced.eq_zero _ ⟨m, hbm⟩
  rw [← hb]
  erw [hb0]
  exact map_zero _

private theorem isRadical_comap_ker_sup_comap_ker {C₁ C₂ : Scheme.{u}}
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced (pullback i₁ i₂)] (z : ↥(pullback i₁ i₂)) (x : X)
    (h₁ : i₁.base ((pullback.fst i₁ i₂).base z) = x)
    (h₂ : i₂.base ((pullback.snd i₁ i₂).base z) = x) :
    ((RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom).IsRadical := by

  let σ₁ : X.presheaf.stalk x →+* C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) :=
    (i₁.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom
  let σ₂ : X.presheaf.stalk x →+* C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) :=
    (i₂.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom
  have hσ₁ : Function.Surjective σ₁ :=
    (i₁.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₁)
  have hσ₂ : Function.Surjective σ₂ :=
    (i₂.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₂)
  have hK₁ : RingHom.ker σ₁ =
      (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom :=
    (RingHom.comap_ker _ _).symm
  have hK₂ : RingHom.ker σ₂ =
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom :=
    (RingHom.comap_ker _ _).symm
  set K := (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom with hKdef
  have hK₁le : RingHom.ker σ₁ ≤ K := hK₁ ▸ le_sup_left
  have hK₂le : RingHom.ker σ₂ ≤ K := hK₂ ▸ le_sup_right

  have hker₁ : RingHom.ker σ₁ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₁
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hker₂ : RingHom.ker σ₂ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₂
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hKmax : K ≤ maximalIdeal _ := sup_le (hK₁ ▸ hker₁) (hK₂ ▸ hker₂)
  have hKtop : K ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top (top_le_iff.mp (h ▸ hKmax))
  haveI : Nontrivial ((X.presheaf.stalk x) ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hKtop
  haveI : IsLocalRing ((X.presheaf.stalk x) ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let α₁ : C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₁le).comp (RingHom.quotientKerEquivOfSurjective hσ₁).symm.toRingHom
  let α₂ : C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₂le).comp (RingHom.quotientKerEquivOfSurjective hσ₂).symm.toRingHom
  have hα₁ : α₁.comp σ₁ = Ideal.Quotient.mk K := by
    ext a
    simp [α₁, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  have hα₂ : α₂.comp σ₂ = Ideal.Quotient.mk K := by
    ext a
    simp [α₂, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  haveI : IsLocalHom α₁ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₁) (by rw [← RingHom.coe_comp, hα₁]; exact Ideal.Quotient.mk_surjective))
  haveI : IsLocalHom α₂ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₂) (by rw [← RingHom.coe_comp, hα₂]; exact Ideal.Quotient.mk_surjective))

  let q : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x
  let a₁ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₁ :=
    Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _
  let a₂ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₂ :=
    Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _
  have hring₁ : (X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ i₁.stalkMap _ ≫ CommRingCat.ofHom α₁ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₁ (σ₁ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₁]
  have hring₂ : (X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫ i₂.stalkMap _ ≫ CommRingCat.ofHom α₂ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₂ (σ₂ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₂]
  have ha₁ : a₁ ≫ i₁ = q := by
    simp only [a₁, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₁)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₁]
    rfl
  have ha₂ : a₂ ≫ i₂ = q := by
    simp only [a₂, q, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₂)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₂]
    rfl
  let g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ pullback i₁ i₂ :=
    pullback.lift a₁ a₂ (ha₁.trans ha₂.symm)
  have hg : g ≫ (pullback.fst i₁ i₂ ≫ i₁) = q := by
    rw [← Category.assoc, pullback.lift_fst, ha₁]
  have hpt : (g ≫ (pullback.fst i₁ i₂ ≫ i₁)).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x := by
    rw [hg]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

  have hw₁ : (pullback.fst i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.fst i₁ i₂).base z := by
    change (g ≫ pullback.fst i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_fst]
    change (Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hw₂ : (pullback.snd i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.snd i₁ i₂).base z := by
    change (g ≫ pullback.snd i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_snd]
    change (Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  refine isRadical_of_specLift (pullback.fst i₁ i₂ ≫ i₁) x K g hg hpt (sup_le ?_ ?_)
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have e : (X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ X.presheaf.stalkSpecializes
          (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom a := by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [Scheme.Hom.stalkMap_comp]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) = 0
    rw [e]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₁ _ _ (specializes_of_eq hw₁), ha, map_zero,
      map_zero]
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have hcond : (pullback.fst i₁ i₂ ≫ i₁).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
        (pullback.snd i₁ i₂ ≫ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) :=
      congrArg (fun k => k.base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))))
        (pullback.condition (f := i₁) (g := i₂))
    rw [Scheme.Hom.stalkMap_congr_hom _ _ pullback.condition, Scheme.Hom.stalkMap_comp]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      (((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a)) = 0
    have e : ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫
          X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom a := by
      change ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          X.presheaf.stalkSpecializes (Inseparable.of_eq hcond).ge).hom a = _
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [e]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₂ _ _ (specializes_of_eq hw₂), ha, map_zero,
      map_zero]

private theorem branchIdeal_sup_eq_transport {x x' ζ₁ ζ₁' ζ₂ ζ₂' : X}
    (ex : x = x') (e₁ : ζ₁ = ζ₁') (e₂ : ζ₂ = ζ₂')
    (g₁ : ζ₁ ⤳ x) (g₂ : ζ₂ ⤳ x) (g₁' : ζ₁' ⤳ x') (g₂' : ζ₂' ⤳ x')
    (H : Scheme.branchIdeal g₁ ⊔ Scheme.branchIdeal g₂ = maximalIdeal (X.presheaf.stalk x)) :
    Scheme.branchIdeal g₁' ⊔ Scheme.branchIdeal g₂' = maximalIdeal (X.presheaf.stalk x') := by
  subst ex e₁ e₂
  exact H

private theorem descent {A Abar B : Type*} [CommRing A] [CommRing Abar] [CommRing B]
    [IsLocalRing A] [IsLocalRing Abar] [IsLocalRing B] [IsReduced B]
    (θ : A →+* Abar) (hθ : Function.Surjective θ) (ψ : Abar →+* B) (hψ : ψ.Flat) [IsLocalHom ψ]
    {P Q : Ideal A} {P' Q' : Ideal B} [P'.IsPrime] [Q'.IsPrime]
    (hP : P'.comap (ψ.comp θ) = P) (hQ : Q'.comap (ψ.comp θ) = Q) (hPQ : P ≠ Q)
    (htri : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 = maximalIdeal B ∨ 𝔮 = P' ∨ 𝔮 = Q')
    (hPm : P' ≠ maximalIdeal B) (hQm : Q' ≠ maximalIdeal B) (hPQ' : ¬ P' ≤ Q') (hQP' : ¬ Q' ≤ P')
    (hκ : P' ⊔ Q' = maximalIdeal B) :
    P ⊔ Q = maximalIdeal A := by
  haveI : IsLocalHom θ := IsLocalHom.of_surjective θ hθ

  have hminP : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ P' → 𝔮 = P' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hPm
    · rfl
    · exact absurd hle hQP'
  have hminQ : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ Q' → 𝔮 = Q' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hQm
    · exact absurd hle hPQ'
    · rfl

  have hkerP : RingHom.ker θ ≤ P := by
    intro a ha
    rw [← hP, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hkerQ : RingHom.ker θ ≤ Q := by
    intro a ha
    rw [← hQ, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hcmP : (P.map θ).comap θ = P := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerP]
  have hcmQ : (Q.map θ).comap θ = Q := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerQ]

  have hPbar : P'.comap ψ = P.map θ := by
    rw [← hP, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  have hQbar : Q'.comap ψ = Q.map θ := by
    rw [← hQ, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  haveI hPbp : (P.map θ).IsPrime := hPbar ▸ Ideal.comap_isPrime ψ P'
  haveI hQbp : (Q.map θ).IsPrime := hQbar ▸ Ideal.comap_isPrime ψ Q'
  have hPQbar : P.map θ ≠ Q.map θ := fun h => hPQ (by rw [← hcmP, h, hcmQ])

  have hmapP : (P.map θ).map ψ = P' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hPbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exact le_rfl
    · exfalso
      rw [hQbar] at hle
      rw [← hPbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ P' hminP hPQbar.symm hle
  have hmapQ : (Q.map θ).map ψ = Q' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hQbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exfalso
      rw [hPbar] at hle
      rw [← hQbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ Q' hminQ hPQbar hle
    · exact le_rfl

  have hbar : P.map θ ⊔ Q.map θ = maximalIdeal Abar := by
    refine sup_eq_maximalIdeal_of_map_maximalIdeal_le ψ hψ (Ideal.IsPrime.ne_top hPbp)
      (Ideal.IsPrime.ne_top hQbp) ?_
    rw [Ideal.map_sup, hmapP, hmapQ, hκ]
    exact Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap ψ).ge
  calc P ⊔ Q = ((P ⊔ Q).map θ).comap θ := by
        rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, eq_comm, sup_eq_left]
        exact hkerP.trans le_sup_left
    _ = maximalIdeal A := by rw [Ideal.map_sup, hbar, maximalIdeal_comap]

end TransvChair

end Unit6

section Main

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal.ModularCurve ModularCurve.DRModelPackage P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal.ModularCurve.DRModelPackage IsLocalRing"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    Scheme.branchIdeal hinf ⊔ Scheme.branchIdeal hzero =
      IsLocalRing.maximalIdeal ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) := by
  classical
  have _ := hp
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  haveI := 𝔛.crossing_reduced κ
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsReduced (baseChangeO p κ) := ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p κ

  have h₁ := compInf_genericPoint_specializes p 𝔛 κ n
  have h₂ := compZero_genericPoint_specializes p 𝔛 κ n
  have hy₂ := compZero_snd_eq_compInf_fst p 𝔛 κ n
  obtain ⟨hy₁', hy₂'⟩ := compInf_genericPoint_ne_and_compZero_genericPoint_ne p 𝔛 κ O toκ n

  have htri := frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal p 𝔛 κ n
  obtain ⟨hPm, hQm, hPQ', hQP'⟩ := frame_branchIdeal_ne_maximalIdeal_and_not_le p 𝔛 κ O hϖ toκ n hy₁' hy₂'

  have hJ₁le : RingHom.ker ((𝔛.compInf κ).stalkMap
      ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom ≤ Scheme.branchIdeal h₁ :=
    TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.compInf κ) (genericPoint_specializes _)
  have hJ₂le : (RingHom.ker ((𝔛.compZero κ).stalkMap
      ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom).comap
      ((baseChangeO p κ).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom ≤
      Scheme.branchIdeal h₂ := by
    refine (Ideal.comap_mono (TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.compZero κ)
      (genericPoint_specializes ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)))).trans
      (le_of_eq ?_)
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_comp]
    rfl

  haveI hJ₁p : (RingHom.ker ((𝔛.compInf κ).stalkMap
      ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p : (RingHom.ker ((𝔛.compZero κ).stalkMap
      ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p' : ((RingHom.ker ((𝔛.compZero κ).stalkMap
      ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom).comap
      ((baseChangeO p κ).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom).IsPrime :=
    Ideal.comap_isPrime _ _
  have hJ₁ : RingHom.ker ((𝔛.compInf κ).stalkMap
      ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom = Scheme.branchIdeal h₁ :=
    eq_branchIdeal_of_isPrime_of_le h₁ h₂ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQP' _ hJ₁le
  have hJ₂ : (RingHom.ker ((𝔛.compZero κ).stalkMap
      ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).hom).comap
      ((baseChangeO p κ).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom =
      Scheme.branchIdeal h₂ :=
    eq_branchIdeal_of_isPrime_of_le h₂ h₁ (fun 𝔮 h𝔮 => (htri 𝔮).imp id Or.symm) hQm hPQ' _ hJ₂le

  have hrad : (Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂).IsRadical := by
    have h := TransvChair.isRadical_comap_ker_sup_comap_ker (𝔛.compInf κ) (𝔛.compZero κ) n _ rfl hy₂
    have e : (baseChangeO p κ).presheaf.stalkSpecializes (specializes_of_eq
        (rfl : (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n) =
          (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))) = 𝟙 _ :=
      (baseChangeO p κ).presheaf.stalkSpecializes_refl _
    rw [e, CommRingCat.hom_id, Ideal.comap_id, hJ₁, hJ₂] at h
    exact h
  have hκ : Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂ = IsLocalRing.maximalIdeal _ :=
    eq_of_isRadical_of_le_of_forall_le hrad
      (sup_le (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)))
      (fun 𝔮 h𝔮 hle => by
        rcases htri 𝔮 with rfl | rfl | rfl
        · exact le_rfl
        · exact absurd (le_sup_right.trans hle) hQP'
        · exact absurd (le_sup_left.trans hle) hPQ')

  have E : (DRModel.baseChangeMap (p := p) toκ).base
        ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)) =
      (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).base
        ((DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ)).base
          ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))) := by
    rw [← Scheme.Hom.comp_apply (DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ))
        (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)),
      TransvL1.baseChangeMap_resLift_comp (p := p) O hϖ κ toκ]
  have hι := (ConcreteCategory.bijective_of_isIso
    ((baseChangeO p O).presheaf.stalkCongr (.of_eq E)).hom).2
  have hπ := TransvL1.stalkMap_baseChangeMap_residue_surjective (p := p) O
    ((DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ)).base
      ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)))
  have hθ : Function.Surjective
      (((baseChangeO p O).presheaf.stalkCongr (.of_eq E)).hom ≫
        (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).stalkMap
          ((DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ)).base
            ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)))).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hπ.comp hι
  have hψ := TransvL1.flat_stalkMap_baseChangeMap_resLift (p := p) O hϖ κ toκ
    ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))
  have hfac : ((DRModel.baseChangeMap (p := p) toκ).stalkMap
        ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))).hom =
      ((DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ)).stalkMap
          ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n))).hom.comp
        (((baseChangeO p O).presheaf.stalkCongr (.of_eq E)).hom ≫
          (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).stalkMap
            ((DRModel.baseChangeMap (p := p) (TransvL1.resLift O hϖ κ toκ)).base
              ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)))).hom := by
    rw [TransvL1.stalkMap_baseChangeMap_eq (p := p) O hϖ κ toκ, CommRingCat.hom_comp,
      CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc]

  have hP := TransvChair.comap_stalkMap_comap_stalkSpecializes (DRModel.baseChangeMap (p := p) toκ) h₁
  have hQ := TransvChair.comap_stalkMap_comap_stalkSpecializes (DRModel.baseChangeMap (p := p) toκ) h₂
  rw [hfac] at hP hQ
  change (Scheme.branchIdeal h₁).comap _ =
    Scheme.branchIdeal ((DRModel.baseChangeMap (p := p) toκ).base.hom.map_specializes h₁) at hP
  change (Scheme.branchIdeal h₂).comap _ =
    Scheme.branchIdeal ((DRModel.baseChangeMap (p := p) toκ).base.hom.map_specializes h₂) at hQ

  have hPQ : Scheme.branchIdeal ((DRModel.baseChangeMap (p := p) toκ).base.hom.map_specializes h₁) ≠
      Scheme.branchIdeal ((DRModel.baseChangeMap (p := p) toκ).base.hom.map_specializes h₂) :=
    fun h => baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint p 𝔛 O hϖ κ toκ
      (by simp only [Scheme.Hom.comp_base, TopCat.comp_app]; exact eq_of_branchIdeal_eq _ _ h)

  have H := TransvChair.descent _ hθ _ hψ hP hQ hPQ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQm hPQ' hQP' hκ

  have ey : (DRModel.baseChangeMap (p := p) toκ).base
      ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)) =
      𝔛.crossingPt O κ toκ n := by
    show _ = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫
      DRModel.baseChangeMap toκ).base n
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have eξ₁ : (DRModel.baseChangeMap (p := p) toκ).base
      ((𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C)) = 𝔛.ξinf O κ toκ := by
    show _ = (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have eξ₂ : (DRModel.baseChangeMap (p := p) toκ).base
      ((𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C)) = 𝔛.ξzero O κ toκ := by
    show _ = (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  exact TransvChair.branchIdeal_sup_eq_transport ey eξ₁ eξ₂ _ _ hinf hzero H

end Main

end S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal (solution)
