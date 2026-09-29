-- Prove2me | solution 1 for ModularCurve.XOneP.pts_heckeGenOne_smul_eq_comp_abelJacobi_of_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c4399da7-5f2b-5dfd-b76e-acf8df01851a

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_XOne_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_ModularCurve_XOneP_exists_curveModel_x1x0FunctionFieldC_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined

import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pts_heckeGenOne_smul_eq_comp_abelJacobi_of_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve P2MW.S_ModularCurve_XOneP_pts_heckeGenOne_smul_eq_comp_abelJacobi_of_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul.AlgebraicCurve"

section SharedHUL
universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degZero Pic Pic0 Pic0.mk Pic0.correspondence Place.restrictAlong CurveModel TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin TwoChartIntegralModel TwoChartIntegralModel.toBase CurveModel.adjoin_simple_inv_eq CurveModel.finiteDimensional_congr TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace toBase C ffEquiv smooth mk glued ι₀ ιInf mem_range_ι₀_or_mem_range_ιInf adjoin_simple_inv_eq finiteDimensional_congr chartRing"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

variable (K : Type u) [Field K] [CharZero K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set L)) L]
  [FiniteDimensional (IntermediateField.adjoin K ({t⁻¹} : Set L)) L]

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({t} : Set L)) L]
  [FiniteDimensional (IntermediateField.adjoin K ({t⁻¹} : Set L)) L] in

theorem ringKrullDim_stalk_le_one_of_isOpenImmersion (A : Subalgebra K L) [IsDedekindDomain A]
    (ι : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ι] (x : Spec (CommRingCat.of A)) :
    ringKrullDim ((glued K t).presheaf.stalk (ι.base x)) ≤ 1 := by
  rw [ringKrullDim_eq_of_ringEquiv (asIso (ι.stalkMap x)).commRingCatIsoToRingEquiv]
  haveI : Ring.DimensionLEOne ((Spec (CommRingCat.of A)).presheaf.stalk x) :=
    Ring.DimensionLEOne.localization (R := A) ((Spec (CommRingCat.of A)).presheaf.stalk x)
      (M := x.asIdeal.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors _)
  have h := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ((Spec (CommRingCat.of A)).presheaf.stalk x))
  exact_mod_cast h

theorem ringKrullDim_stalk_glued_le_one (y : glued K t) : ringKrullDim ((glued K t).presheaf.stalk y) ≤ 1 := by
  rcases mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ringKrullDim_stalk_le_one_of_isOpenImmersion K t (chartRing K ({t} : Set L)) (ι₀ K t) x
  · exact ringKrullDim_stalk_le_one_of_isOpenImmersion K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t) x

end AlgebraicCurve.CurveModel

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degZero Pic Pic0 Pic0.mk Pic0.correspondence Place.restrictAlong CurveModel TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin TwoChartIntegralModel TwoChartIntegralModel.toBase CurveModel.adjoin_simple_inv_eq CurveModel.finiteDimensional_congr TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "pointEquivPlace_eq_restrictAlong_of_chartPin chartAlgFin ιFin ιInf toBase baseChange fibre exists_iso_glued_pullback_toBase_of_isFractionRing"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

theorem ringKrullDim_stalk_le_one_of_asIdeal_eq_bot
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)]
    [FiniteDimensional (IntermediateField.adjoin K₀ ({j} : Set F)) F]
    [FiniteDimensional (IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (e : X ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (he : e.hom ≫ toBase R F j = f) (x : X) (hx : (f.base x).asIdeal = ⊥) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  obtain ⟨-, h2⟩ := AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing K₀ f

  suffices H : ∀ w : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))),
      ringKrullDim ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))).presheaf.stalk w) ≤ 1 by
    let m : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) :=
      pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) (toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) e.hom (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, he]) (by rw [Category.comp_id, Category.id_comp])
    have H' : ∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))),
        ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))).presheaf.stalk y) ≤ (1 : ℕ) := by
      intro y
      rw [← ringKrullDim_eq_of_ringEquiv (asIso (m.stalkMap y)).commRingCatIsoToRingEquiv]
      exact_mod_cast H (m.base y)
    exact_mod_cast h2 1 H' x hx
  obtain ⟨es, hes, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing R K₀ F j
  intro w
  obtain ⟨z, rfl⟩ : ∃ z, es.base z = w :=
    ⟨(inv es).base w, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [ringKrullDim_eq_of_ringEquiv (asIso (es.stalkMap z)).commRingCatIsoToRingEquiv]
  exact AlgebraicCurve.CurveModel.ringKrullDim_stalk_glued_le_one K₀ j z

end AlgebraicCurve.TwoChartIntegralModel

namespace ModularCurve p2m_export "ModularCurve" "TwoChart.chartAlgFin TwoChartModel TwoChart.ιFin TwoChart.modelTo x1FunctionField x1x0FunctionFieldC x1FunctionFieldBar JOne arithmeticGalois qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff heckeGenOne heckeOperatorOneBar_apply HeckeDiamondCommuteBar HeckeDiamondInputsAll heckeModuleOneBar heckeModuleOneBar_heckeGenOne_smul heckeAlphaOneBar coe_heckeAlphaOneBar heckeBetaOneBar coe_heckeBetaOneBar heckeOperatorOneAlong heckeOperatorOneAlong_eq XOne.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange XOneP.exists_curveModel_x1x0FunctionFieldC_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange" namespace XOneP p2m_export "ModularCurve.XOneP" "exists_curveModel_x1x0FunctionFieldC_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul" end ModularCurve.XOneP
p2m_open_scoped "ModularCurve ModularCurve.XOneP" in

theorem ModularCurve.XOneP.mem_of_asIdeal_eq_bot_of_ringKrullDim_le_one_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens)
    (hUdim : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U) :
    ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ((ModularCurve.TwoChart.modelTo A (↥K) j).base x).asIdeal = ⊥ → x ∈ U := by
  intro x hx
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  haveI : FiniteDimensional ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K :=
    AlgebraicCurve.CurveModel.finiteDimensional_congr L (AlgebraicCurve.CurveModel.adjoin_simple_inv_eq L j).symm
  obtain ⟨e, he, -, -⟩ := ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A (↥K) j
  exact hUdim x (AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_one_of_asIdeal_eq_bot A L (↥K) j
    (ModularCurve.TwoChart.modelTo A (↥K) j) e he x hx)

p2m_open_scoped "ModularCurve ModularCurve.XOneP" in
open AlgebraicGeometry.SmoothProperCurve in

theorem ModularCurve.XOneP.range_fst_specMap_subset_of_ringKrullDim_le_one_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens)
    (hUdim : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U) :
    Set.range (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)).base ⊆
      (U : Set ↥(ModularCurve.TwoChartModel A (↥K) j)) := by
  rintro _ ⟨y, rfl⟩
  refine ModularCurve.XOneP.mem_of_asIdeal_eq_bot_of_ringKrullDim_le_one_twoChartModel_x1_mul
    p M L K hK A j hj U hUdim _ ?_
  have key : ∀ z : ↥(Spec (CommRingCat.of L)), Ideal.comap (algebraMap A L) z.asIdeal = ⊥ := fun z => by
    rw [(Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A L)
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    CommRingCat.hom_ofHom]
  exact key _

end SharedHUL

noncomputable section

namespace GenAwayBody

universe u

private def castBase {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s') (a : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨a.1, a.2.trans e⟩

private theorem castBase_coe {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s')
    (a : SchemeHomOver s f) : (castBase e a).1 = a.1 := rfl

private theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (a b : SchemeHomOver s f) :
    G.mul s' (castBase e a) (castBase e b) = castBase e (G.mul s a b) := by
  subst e; rfl

private def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

private theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

private theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

private theorem liftPt_mul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a b : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    liftPt D R' t ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (t ≫ specMap R R') a b) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t
        (liftPt D R' t a) (liftPt D R' t b) := by
  symm
  apply eq_liftPt
  exact AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t _ _ a b
    (liftPt_fst D R' t a).symm (liftPt_fst D R' t b).symm

private def liftEquiv {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R') :
    SchemeHomOver s D.toBase ≃ SchemeHomOver t (D.baseChange R').toBase where
  toFun a := liftPt D R' t (castBase hs a)
  invFun z := ⟨z.1 ≫ pullback.fst D.toBase (specMap R R'), by
    rw [Category.assoc, pullback.condition, reassoc_of% z.2, hs]⟩
  left_inv a := Subtype.ext (liftPt_fst D R' t (castBase hs a))
  right_inv z := (eq_liftPt D R' t z _ rfl).symm

private theorem liftEquiv_apply {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R')
    (a : SchemeHomOver s D.toBase) : liftEquiv D R' t hs a = liftPt D R' t (castBase hs a) := rfl

private theorem liftEquiv_apply_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R')
    (a : SchemeHomOver s D.toBase) :
    (liftEquiv D R' t hs a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  liftPt_fst D R' t (castBase hs a)

private theorem isPullback_fst_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback c t)
  · rw [curveChange_snd, hf]
    exact IsPullback.of_hasPullback c' t
  · simp only [curveChange, pullback.lift_fst]

private theorem curveChange_fst {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

private theorem isIso_lift_of_comp {X S T T' : Scheme.{u}} (f : X ⟶ S) (u : T ⟶ S) (v : T' ⟶ T) (w : T' ⟶ S)
    (hw : w = v ≫ u) (k : pullback f w ⟶ pullback f u)
    (hk₁ : k ≫ pullback.fst f u = pullback.fst f w) (hk₂ : k ≫ pullback.snd f u = pullback.snd f w ≫ v)
    (hk : k ≫ pullback.snd f u = pullback.snd f w ≫ v) :
    IsIso (pullback.lift k (pullback.snd f w) hk : pullback f w ⟶ pullback (pullback.snd f u) v) := by
  refine ⟨⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst f u) (pullback.snd _ _) ?_, ?_, ?_⟩⟩
  · rw [hw, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hk₁, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hk₁, pullback.lift_fst]
      · rw [Category.assoc, hk₂, pullback.lift_snd_assoc, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

section K

private abbrev cls {X : Scheme.{u}} (M : X.Modules) : Skeleton X.Modules := toSkeleton M

private theorem cls_eq_iff {X : Scheme.{u}} (A B : X.Modules) : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun ⟨e⟩ => Quotient.sound ⟨e⟩⟩

private theorem cls_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) : cls A = cls B :=
  (cls_eq_iff A B).2 ⟨e⟩

private noncomputable def isoOfClsEq {X : Scheme.{u}} {A B : X.Modules} (h : cls A = cls B) : A ≅ B :=
  ((cls_eq_iff A B).1 h).some

private theorem cls_tensor {X : Scheme.{u}} (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B :=
  Skeleton.toSkeleton_tensorObj A B

private theorem cls_unit (X : Scheme.{u}) : cls (𝟙_ X.Modules) = 1 := Skeleton.one_eq.symm

private theorem cls_pullback_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (h : cls A = cls B) :
    cls ((Scheme.Modules.pullback f).obj A) = cls ((Scheme.Modules.pullback f).obj B) :=
  cls_congr ((Scheme.Modules.pullback f).mapIso (isoOfClsEq h))

private theorem cls_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj (A ⊗ B)) =
      cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B) :=
  (cls_congr (Scheme.Modules.pullbackTensorObjIso f A B)).trans (cls_tensor _ _)

private theorem cls_pullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cls ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.pullbackTensorUnitObjIso f)).trans (cls_unit X)

private theorem cls_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    cls ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
      cls ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
  cls_congr ((Scheme.Modules.pullbackComp f g).app M)

private theorem cls_pullback_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj M) = cls ((Scheme.Modules.pullback g).obj M) := by
  subst h; rfl

private theorem cls_pullback_id {X : Scheme.{u}} (M : X.Modules) :
    cls ((Scheme.Modules.pullback (𝟙 X)).obj M) = cls M :=
  cls_congr ((Scheme.Modules.pullbackId X).app M)

private theorem cls_pullback_inv_hom {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : Y.Modules) :
    cls ((Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.inv_hom_id e), cls_pullback_id]

private theorem cls_pullback_hom_inv {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : X.Modules) :
    cls ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (inv e)).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.hom_inv_id e), cls_pullback_id]

private theorem cls_normModule_congr {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (h : cls L = cls L') :
    cls (Scheme.Modules.normModule π d L) = cls (Scheme.Modules.normModule π d L') :=
  cls_congr (Scheme.Modules.normModuleMapIso π d (isoOfClsEq h))

end K

private theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

private theorem exists_isPullback_curveChange_restrict {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) (U : C.Opens) :
    ∃ k : ↑((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)) ⟶ ↑(f ⁻¹ᵁ U),
      IsPullback k (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) (f ∣_ U) (pullback.fst c t ∣_ U) := by
  have s : IsPullback
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t)
      (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) f (((pullback.fst c t) ⁻¹ᵁ U).ι ≫ pullback.fst c t) :=
    (isPullback_morphismRestrict (curveChange f hf t) ((pullback.fst c t) ⁻¹ᵁ U)).flip.paste_horiz
      (isPullback_fst_curveChange f hf t)
  have w : (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U ≫ pullback.fst c t ∣_ U) ≫ U.ι =
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t) ≫ f := by
    rw [Category.assoc, morphismRestrict_ι]
    exact s.w.symm
  refine ⟨(isPullback_morphismRestrict f U).lift _ _ w, ?_⟩
  refine IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ (IsPullback.lift_fst _ _ _ _)
    (isPullback_morphismRestrict f U).flip
  rw [IsPullback.lift_snd, morphismRestrict_ι]
  exact s

private theorem flat_of_flat_morphismRestrict_of_eq_top {X S : Scheme.{u}} (g : X ⟶ S) (V : S.Opens) (hV : V = ⊤)
    [Flat (g ∣_ V)] : Flat g := by
  subst hV
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) (fun _ : Unit => (⊤ : S.Opens)) (by simp) (fun _ => inferInstance)

theorem coeffMap_mem_laurentBaseChange' (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K : IntermediateField L (LaurentSeries L)) (hK : K = ModularCurve.laurentBaseChange L F₀) (b : ↥K) :
    ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀ := by
  have hx : ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L F₀ := hK ▸ b.2
  rw [ModularCurve.mem_laurentBaseChange_iff] at hx
  generalize ((b : ↥K) : LaurentSeries L) = x at hx ⊢
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single,
          ← ModularCurve.algebraMap_laurentSeries_eq_single]
        exact (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀).algebraMap_mem _
      · have hcomp : (algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ) :=
          Subsingleton.elim _ _
        rw [ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hcomp]
        exact ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

private theorem coeffMap_qExpandₓ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff]
  · rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd n _ hk, ModularCurve.qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

end GenAwayBody

open GenAwayBody in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens)
    (hsurjα : Function.Surjective πα.1.base) (hsurjβ : Function.Surjective πβ.1.base)
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (hsqα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hsqβ : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hpreα : πα.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hpreβ : πβ.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hUdim : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U)
    (hflα : Flat (πα.1 ∣_ U)) (hflβ : Flat (πβ.1 ∣_ U))
    (hrkα : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))

    (𝒩 : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Modules) (h𝒩 : Scheme.Modules.IsInvertible 𝒩)
    (hNe : ∀ (V : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Opens) (d' : ℕ),
      Flat ((curveChange πα.1 πα.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πα.1 πα.2 D.toBase) ∣_ V) →
      (∀ y : V, ((curveChange πα.1 πα.2 D.toBase) ∣_ V).finrank y = d') →
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
        Scheme.Modules.normModule ((curveChange πα.1 πα.2 D.toBase) ∣_ V) d'
          ((Scheme.Modules.pullback ((curveChange πα.1 πα.2 D.toBase) ⁻¹ᵁ V).ι).obj
            ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hrep.some.poincare.L))))
    (Tℓ : SchemeHomOver D.toBase D.toBase)
    (hTℓ : Nonempty ((hrep.some.poincare.pullbackAlong Tℓ).L ≅
      Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase) 𝒩))
    (hTℓmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) Tℓ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x Tℓ) (NeronModelInfra.schemeHomOverComp y Tℓ)) :
    letI := ModularCurve.heckeModuleOneBar (M * p)
    ∀ x : ModularCurve.JOne (M * p), (gpts (ModularCurve.heckeGenOne ⟨ℓ, Fact.out⟩ • x)).1 = (gpts x).1 ≫ Tℓ.1 := by
  classical
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M * p * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * p)) (Fact.out : ℓ.Prime).ne_zero⟩

  obtain ⟨Mη', eηr, hiso', Mη'_chart_nonempty, heηr, hMη'pin, -⟩ :=
    ModularCurve.XOneP.exists_curveModel_x1x0FunctionFieldC_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ℓ jℓ hjℓ
  haveI := hiso'
  haveI := Mη'_chart_nonempty
  haveI : Surjective πα.1 := ⟨hsurjα⟩
  haveI : Surjective πβ.1 := ⟨hsurjβ⟩

  haveI : IsProper (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) := hsmL
  haveI : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) := hgiL

  haveI hfa : IsFinite (curveChange πα.1 πα.2 (specMap A L)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange πα.1 πα.2 (specMap A L)) inferInstance
  haveI hfb : IsFinite (curveChange πβ.1 πβ.2 (specMap A L)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange πβ.1 πβ.2 (specMap A L)) inferInstance
  haveI hla : LocallyOfFinitePresentation (curveChange πα.1 πα.2 (specMap A L)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange πα.1 πα.2 (specMap A L)) inferInstance
  haveI hlb : LocallyOfFinitePresentation (curveChange πβ.1 πβ.2 (specMap A L)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange πβ.1 πβ.2 (specMap A L)) inferInstance

  have hUL : Set.range (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)).base ⊆ (U : Set ↥(ModularCurve.TwoChartModel A (↥K) j)) :=
    ModularCurve.XOneP.range_fst_specMap_subset_of_ringKrullDim_le_one_twoChartModel_x1_mul p M L K hK A j hj U hUdim
  have hVtop : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) ⁻¹ᵁ U = ⊤ :=
    top_le_iff.mp fun y _ => hUL ⟨y, rfl⟩
  haveI : Flat (πα.1 ∣_ U) := hflα
  haveI : Flat (πβ.1 ∣_ U) := hflβ
  obtain ⟨kα, sqα⟩ := exists_isPullback_curveChange_restrict πα.1 πα.2 (specMap A L) U
  obtain ⟨kβ, sqβ⟩ := exists_isPullback_curveChange_restrict πβ.1 πβ.2 (specMap A L) U
  haveI hflaV : Flat (curveChange πα.1 πα.2 (specMap A L) ∣_ (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback sqα inferInstance
  haveI hflbV : Flat (curveChange πβ.1 πβ.2 (specMap A L) ∣_ (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback sqβ inferInstance
  haveI hfla : Flat (curveChange πα.1 πα.2 (specMap A L)) := flat_of_flat_morphismRestrict_of_eq_top _ _ hVtop
  haveI hflb : Flat (curveChange πβ.1 πβ.2 (specMap A L)) := flat_of_flat_morphismRestrict_of_eq_top _ _ hVtop
  have hrka : ∀ y, (curveChange πα.1 πα.2 (specMap A L)).finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1) := by
    intro y
    have hyU : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)).base y ∈ U := hUL ⟨y, rfl⟩
    rw [← Scheme.Hom.finrank_morphismRestrict_eq_finrank (curveChange πα.1 πα.2 (specMap A L))
      ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) ⁻¹ᵁ U) y hyU,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ sqα ⟨y, hyU⟩]
    have hy : ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) ∣_ U).base ⟨y, hyU⟩ =
        ⟨(pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)).base y, hyU⟩ :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    rw [hy, Scheme.Hom.finrank_morphismRestrict_eq_finrank]
    exact hrkα _ hyU
  have hαc : curveChange πα.1 πα.2 (specMap A L) ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L =
      baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L := curveChange_snd πα.1 πα.2 _
  have hβc : curveChange πβ.1 πβ.2 (specMap A L) ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L =
      baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L := curveChange_snd πβ.1 πβ.2 _

  let φη : SchemeHomOver (D.baseChange L).toBase (D.baseChange L).toBase :=
    ⟨pullback.map D.toBase (specMap A L) D.toBase (specMap A L) Tℓ.1 (𝟙 _) (𝟙 _)
      (by rw [Tℓ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]),
     by simp only [pullback.lift_snd, Category.comp_id]⟩
  have hφfst : φη.1 ≫ pullback.fst D.toBase (specMap A L) = pullback.fst _ _ ≫ Tℓ.1 := pullback.lift_fst _ _ _
  have hcomp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of L)) (a : SchemeHomOver (s ≫ specMap A L) D.toBase),
      NeronModelInfra.schemeHomOverComp (liftPt D L s a) φη = liftPt D L s (NeronModelInfra.schemeHomOverComp a Tℓ) := by
    intro T s a
    apply eq_liftPt
    change ((liftPt D L s a).1 ≫ φη.1) ≫ _ = a.1 ≫ Tℓ.1
    rw [Category.assoc, hφfst, ← Category.assoc, liftPt_fst]
  have hlift : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of L)) (z : SchemeHomOver s (D.baseChange L).toBase),
      ∃ a : SchemeHomOver (s ≫ specMap A L) D.toBase, z = liftPt D L s a := fun s z =>
    ⟨⟨z.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% z.2]⟩, eq_liftPt D L s z _ rfl⟩
  have hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver s (D.baseChange L).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDL).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDL).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη) := by
    intro T s x y
    obtain ⟨a, rfl⟩ := hlift s x
    obtain ⟨b, rfl⟩ := hlift s y
    rw [← liftPt_mul _ _ D hrep.some L hDL hPL, hcomp, hcomp, hcomp, hTℓmul, liftPt_mul _ _ D hrep.some L hDL hPL]

  have hgen : specMap A (AlgebraicClosure ℚ) = specMap L (AlgebraicClosure ℚ) ≫ specMap A L := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  let kL' : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶
      pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (specMap L (AlgebraicClosure ℚ)) :=
    pullback.lift kL (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) (by exact hkL₂)
  have hkL'₁ : kL' ≫ pullback.fst _ _ = kL := pullback.lift_fst _ _ _
  have hkL'₂ : kL' ≫ pullback.snd _ _ = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := pullback.lift_snd _ _ _
  haveI : IsIso kL' := isIso_lift_of_comp _ _ _ _ hgen kL hkL₁ hkL₂ _
  let eηL := eη ≫ kL'
  have heηL : eηL ≫ pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (specMap L (AlgebraicClosure ℚ)) = Mη.toBase := by
    simp only [eηL, Category.assoc, hkL'₂]; exact heη

  let kR : pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A L) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specMap L (AlgebraicClosure ℚ))
      (by rw [pullback.condition, Category.assoc, ← hgen])
  have hkL₂₁ : kR ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hkL₂₂ : kR ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specMap L (AlgebraicClosure ℚ) := pullback.lift_snd _ _ _
  let kR' : pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A (AlgebraicClosure ℚ)) ⟶
      pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L) (specMap L (AlgebraicClosure ℚ)) :=
    pullback.lift kR (pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A (AlgebraicClosure ℚ))) hkL₂₂
  haveI : IsIso kR' := isIso_lift_of_comp _ _ _ _ hgen kR hkL₂₁ hkL₂₂ _
  let eη'L := eηr ≫ kR'
  have heη'L : eη'L ≫ pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L) (specMap L (AlgebraicClosure ℚ)) =
      Mη'.toBase := by
    simp only [eη'L, kR', Category.assoc, pullback.lift_snd]; exact heηr

  have hread : ∀ (a : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a Tℓ)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
          (Scheme.Modules.normModule (curveChange πα.1 πα.2 (specMap A (AlgebraicClosure ℚ))) (if ℓ ∣ M * p then ℓ else ℓ + 1)
            ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 (specMap A (AlgebraicClosure ℚ)))).obj (hrep.some.poincare.pullbackAlong a).L))) :=
    fun a => AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
      hrep.some πα πβ U (if ℓ ∣ M * p then ℓ else ℓ + 1) hflα hrkα
      𝒩 h𝒩 hNe
      Tℓ hTℓ (specMap A (AlgebraicClosure ℚ)) a
      (by
        rintro _ ⟨x, rfl⟩
        rw [← hkL₁, Scheme.Hom.comp_base, TopCat.comp_app]
        exact hUL ⟨_, rfl⟩)
  have hφpt : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) (D.baseChange L).toBase,
      Nonempty ((hDL.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp z φη)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) (sectionBaseChange L ε))
          (pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))))
          (Scheme.Modules.normModule
            (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))))) (if ℓ ∣ M * p then ℓ else ℓ + 1)
            ((Scheme.Modules.pullback
              (curveChange (curveChange πβ.1 πβ.2 (specMap A L)) hβc (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))))).obj
              (hDL.poincare.pullbackAlong z).L))) := by

    have hUt : Set.range (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)).base ⊆
        (U : Set ↥(ModularCurve.TwoChartModel A (↥K) j)) := by
      let k0 : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap L (AlgebraicClosure ℚ) ≫ specMap A L) ⟶
          pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) :=
        pullback.map _ _ _ _ (𝟙 _) (specMap L (AlgebraicClosure ℚ)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])
      have hk0 : k0 ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝟙 _ := pullback.lift_fst _ _ _
      rintro _ ⟨x, rfl⟩
      apply hUL
      refine ⟨k0.base x, ?_⟩
      have := congrArg (fun f => f.base x) hk0
      simpa using this

    intro z
    obtain ⟨a, rfl⟩ := hlift _ z
    have e3 := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
      hrep.some πα πβ U (if ℓ ∣ M * p then ℓ else ℓ + 1) hflα hrkα
      𝒩 h𝒩 hNe
      Tℓ hTℓ (specMap L (AlgebraicClosure ℚ) ≫ specMap A L) a hUt
    rcases e3 with ⟨e3⟩
    rcases poincare_liftPt_iso (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some L hDL hPL (specMap L (AlgebraicClosure ℚ))
      (NeronModelInfra.schemeHomOverComp a Tℓ) with ⟨e1⟩
    rcases poincare_liftPt_iso (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some L hDL hPL (specMap L (AlgebraicClosure ℚ)) a with ⟨e2⟩
    rw [hcomp]

    have sqα : (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))).hom ≫
        curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L) =
        curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [curveChange_fst, reassoc_of% (BaseChange.κ_hom_fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))),
          BaseChange.κ_hom_fst,
          reassoc_of% (curveChange_fst (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ))),
          curveChange_fst]
      · simp only [Category.assoc]
        rw [curveChange_snd, BaseChange.κ_hom_snd, BaseChange.κ_hom_snd, curveChange_snd]
    have sqβ : (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))).hom ≫
        curveChange πβ.1 πβ.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L) =
        curveChange (curveChange πβ.1 πβ.2 (specMap A L)) hβc (specMap L (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [curveChange_fst, reassoc_of% (BaseChange.κ_hom_fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))),
          BaseChange.κ_hom_fst,
          reassoc_of% (curveChange_fst (curveChange πβ.1 πβ.2 (specMap A L)) hβc (specMap L (AlgebraicClosure ℚ))),
          curveChange_fst]
      · simp only [Category.assoc]
        rw [curveChange_snd, BaseChange.κ_hom_snd, BaseChange.κ_hom_snd, curveChange_snd]

    haveI : IsFinite (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange _ hαc _) inferInstance
    haveI : Flat (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @Flat) (isPullback_fst_curveChange _ hαc _) inferInstance
    haveI : LocallyOfFinitePresentation (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange _ hαc _) inferInstance
    have hπαt : curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L) =
        (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))).inv ≫
          curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom := by
      rw [← sqα, Iso.inv_hom_id_assoc]
    haveI : IsFinite (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)) := by
      rw [hπαt]; infer_instance
    haveI : Flat (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)) := by
      rw [hπαt]; infer_instance
    haveI : LocallyOfFinitePresentation (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)) := by
      rw [hπαt]; infer_instance
    have hd : ∀ y, (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)).finrank y =
        (if ℓ ∣ M * p then ℓ else ℓ + 1) := by
      intro y
      rw [hπαt, Scheme.Hom.finrank_comp_left_of_isIso]
      have sq : IsPullback (𝟙 _)
          (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)) ≫
            (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom)
          (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)))
          (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).inv :=
        IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
      exact (Scheme.Hom.finrank_pullbackMap_of_comp_eq _ _ _ _ hαc _).trans (hrka _)
    rcases AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
      (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L)) (if ℓ ∣ M * p then ℓ else ℓ + 1) hd
      (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom
      (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)))
      (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L (specMap L (AlgebraicClosure ℚ))).hom
      (IsPullback.of_horiz_isIso ⟨sqα⟩)
      (((hrep.some.poincare.pullbackAlong a).isInvertible).pullback
        (curveChange πβ.1 πβ.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L))) with ⟨e4⟩

    have hi : cls ((Scheme.Modules.pullback (BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ))).hom).obj
        (Scheme.Modules.normModule (curveChange πα.1 πα.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L))
          (if ℓ ∣ M * p then ℓ else ℓ + 1)
          ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 (specMap L (AlgebraicClosure ℚ) ≫ specMap A L))).obj
            (hrep.some.poincare.pullbackAlong a).L))) =
        cls (Scheme.Modules.normModule
          (curveChange (curveChange πα.1 πα.2 (specMap A L)) hαc (specMap L (AlgebraicClosure ℚ)))
          (if ℓ ∣ M * p then ℓ else ℓ + 1)
          ((Scheme.Modules.pullback
            (curveChange (curveChange πβ.1 πβ.2 (specMap A L)) hβc (specMap L (AlgebraicClosure ℚ)))).obj
            (hDL.poincare.pullbackAlong (liftPt D L (specMap L (AlgebraicClosure ℚ)) a)).L)) := by
      rw [cls_congr e4]
      apply cls_normModule_congr
      rw [cls_pullback_comp, cls_pullback_congr_hom sqβ, ← cls_pullback_comp,
        cls_pullback_congr (curveChange (curveChange πβ.1 πβ.2 (specMap A L)) hβc (specMap L (AlgebraicClosure ℚ)))
          (cls_congr e2)]
    refine (cls_eq_iff _ _).1 ?_
    rw [cls_congr e1, cls_pullback_congr _ (cls_congr e3), Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def,
      cls_pullback_tensor, cls_tensor, hi]
    congr 1
    rw [cls_pullback_comp, cls_pullback_congr_hom (BaseChange.κ_hom_snd (ModularCurve.TwoChart.modelTo A (↥K) j) L (specMap L (AlgebraicClosure ℚ)))]
    apply cls_pullback_congr
    refine cls_congr (Scheme.Modules.dualMapIso (isoOfClsEq ?_))
    rw [cls_pullback_congr_hom (BaseChange.rigSection_κ_hom (ModularCurve.TwoChart.modelTo A (↥K) j) ε L (specMap L (AlgebraicClosure ℚ))).symm,
      ← cls_pullback_comp,
      cls_pullback_congr (rigSection (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (specMap L (AlgebraicClosure ℚ))
        (sectionBaseChange L ε)) hi]

  let pts' := gpts.trans (liftEquiv D L (specMap L (AlgebraicClosure ℚ)) hgen)
  have e1 : ∀ y, (pts' y).1 ≫ pullback.fst D.toBase (specMap A L) = (gpts y).1 := fun y =>
    liftEquiv_apply_fst D L (specMap L (AlgebraicClosure ℚ)) hgen (gpts y)
  have e2 : ∀ y, (pts' y).1 ≫ pullback.snd D.toBase (specMap A L) = specMap L (AlgebraicClosure ℚ) := fun y =>
    (pts' y).2
  have hadd' : ∀ x y : ModularCurve.JOne (M * p), pts' (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDL).mul _ (pts' x) (pts' y) := by
    intro x y
    show liftEquiv D L _ hgen (gpts (x + y)) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDL).mul _
        (liftEquiv D L _ hgen (gpts x)) (liftEquiv D L _ hgen (gpts y))
    rw [hgadd, liftEquiv_apply, liftEquiv_apply, liftEquiv_apply, ← mul_castBase,
      liftPt_mul _ _ D hrep.some L hDL hPL]
  have hnorm' : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eηL ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) _ =
        Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))) ≫ (sectionBaseChange L ε).1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts' (Pic0.mk Dv)).1 = x.1 ≫ eηL ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) _ ≫ ajL.1 := by
    intro x s hs
    have hs' : s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 := by
      have := congrArg (· ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) hs
      simp only [eηL, Category.assoc, sectionBaseChange_coe_fst] at this
      rw [reassoc_of% hkL'₁, hkL₁] at this
      rw [this, hgen, Category.assoc]
    obtain ⟨Dv, hDv, hpts⟩ := hpts_aj x s hs'
    refine ⟨Dv, hDv, ?_⟩
    apply pullback.hom_ext
    · rw [e1, hpts, hajbar]
      simp only [eηL, Category.assoc]
      rw [reassoc_of% hkL'₁]
    · rw [e2]
      symm
      simp only [eηL, Category.assoc]
      have h2 : ajL.1 ≫ pullback.snd D.toBase (specMap A L) = baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L := ajL.2
      have h3 : pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (specMap L (AlgebraicClosure ℚ)) ≫
          baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L = pullback.snd _ _ ≫ specMap L (AlgebraicClosure ℚ) := pullback.condition
      rw [h2, h3, reassoc_of% hkL'₂, reassoc_of% heη, reassoc_of% x.2]

  obtain ⟨-, hαI, hβI, hPD, hfin, hFI, hN⟩ := hin.1 ⟨ℓ, Fact.out⟩
  haveI := hPD
  have hop : ∀ x : ModularCurve.JOne (M * p),
      (letI := ModularCurve.heckeModuleOneBar (M * p); ModularCurve.heckeGenOne ⟨ℓ, Fact.out⟩ • x) =
      Pic0.correspondence (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) ℓ)
        hβI hαI hFI hfin hN x := by
    intro x
    rw [ModularCurve.heckeModuleOneBar_heckeGenOne_smul hcomm, ModularCurve.heckeOperatorOneBar_apply]
    show ModularCurve.heckeOperatorOneAlong (AlgebraicClosure ℚ) (M * p) ℓ x = _
    rw [ModularCurve.heckeOperatorOneAlong_eq (hin.1 ⟨ℓ, Fact.out⟩).1 hαI hβI hFI hfin hN]
    rfl
  have hmemK : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L) ∈ ModularCurve.x1FunctionFieldBar (M * p) :=
    fun a => coeffMap_mem_laurentBaseChange' L (ModularCurve.x1FunctionField (M * p)) K hK a
  have hmemR : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ),
      ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) ∈
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)) :=
    fun b => coeffMap_mem_laurentBaseChange' L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)) (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) rfl b
  haveI hisoT : IsIso (show Mη.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) from eη) := ‹IsIso eη›
  haveI hisoT' : IsIso (show Mη'.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)
      (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) from eηr) := ‹IsIso eηr›

  have hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη'L ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L) _ ≫ curveChange πα.1 πα.2 (specMap A L) =
        x.1 ≫ eηL ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) _ →
      Mη.pointEquivPlace x = Place.restrictAlong (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) hαI (Mη'.pointEquivPlace y) := by
    intro y x hyx
    have hrel : x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        y.1 ≫ eηr ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A (AlgebraicClosure ℚ)) ≫ πα.1 := by
      have := congrArg (· ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) hyx
      simp only [eηL, eη'L, kR', Category.assoc, curveChange_fst, pullback.lift_fst_assoc] at this
      rw [reassoc_of% hkL'₁, hkL₁, reassoc_of% hkL₂₁] at this
      exact this.symm
    exact AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin A (AlgebraicClosure ℚ) (↥K) j
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ
      (L := ↥(ModularCurve.x1FunctionFieldBar (M * p))) (L' := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
      (fun a => ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L), hmemK a⟩)
      (fun b => ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L), hmemR b⟩)
      Mη eη heη Mη_chart_nonempty (fun a => Subtype.ext (hMηpin a))
      Mη' eηr heηr Mη'_chart_nonempty (fun b => Subtype.ext (hMη'pin b))
      πα.1 πα.2 ια hsqα
      (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) (fun a => Subtype.ext (by rw [ModularCurve.coe_heckeAlphaOneBar]; exact congrArg (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ))) (hια a).symm)) hαI hfin y x hrel

  have hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη'L ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L) _ ≫ curveChange πβ.1 πβ.2 (specMap A L) =
        x.1 ≫ eηL ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) _ →
      Mη.pointEquivPlace x = Place.restrictAlong (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) hβI (Mη'.pointEquivPlace y) := by
    intro y x hyx
    have hrel : x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        y.1 ≫ eηr ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A (AlgebraicClosure ℚ)) ≫ πβ.1 := by
      have := congrArg (· ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) hyx
      simp only [eηL, eη'L, kR', Category.assoc, curveChange_fst, pullback.lift_fst_assoc] at this
      rw [reassoc_of% hkL'₁, hkL₁, reassoc_of% hkL₂₁] at this
      exact this.symm
    exact AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin A (AlgebraicClosure ℚ) (↥K) j
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ
      (L := ↥(ModularCurve.x1FunctionFieldBar (M * p))) (L' := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
      (fun a => ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L), hmemK a⟩)
      (fun b => ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L), hmemR b⟩)
      Mη eη heη Mη_chart_nonempty (fun a => Subtype.ext (hMηpin a))
      Mη' eηr heηr Mη'_chart_nonempty (fun b => Subtype.ext (hMη'pin b))
      πβ.1 πβ.2 ιβ hsqβ
      (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) (fun a => Subtype.ext (by
        rw [ModularCurve.coe_heckeBetaOneBar (M * p) ℓ (hin.1 ⟨ℓ, Fact.out⟩).1]
        show ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L)) =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) (((ιβ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L)
        rw [hιβ, coeffMap_qExpandₓ])) hβI (ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined (AlgebraicClosure ℚ) (M * p) ℓ (hin.1 ⟨ℓ, Fact.out⟩).1) y x hrel

  intro x
  have key := ModularCurve.XOne.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange L (M * p)
    (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε) (D.baseChange L) hDL ajL hajLε hajL
    Mη eηL heηL (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))
    (pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A L)) (baseChange A (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) L)
    (curveChange πα.1 πα.2 (specMap A L)) (curveChange πβ.1 πβ.2 (specMap A L)) hαc hβc
    (if ℓ ∣ M * p then ℓ else ℓ + 1) hrka φη hφpt hφadd Mη' eη'L heη'L
    (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) hαI
    (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) ℓ) hβI
    hplaceα hplaceβ hFI hfin hN pts' hadd' hnorm' x
  rw [hop]
  calc (gpts _).1 = (pts' _).1 ≫ pullback.fst D.toBase (specMap A L) := (e1 _).symm
    _ = ((pts' x).1 ≫ φη.1) ≫ pullback.fst D.toBase (specMap A L) := by rw [key]
    _ = (gpts x).1 ≫ Tℓ.1 := by rw [Category.assoc, hφfst, ← Category.assoc, e1]

end

end S_ModularCurve_XOneP_pts_heckeGenOne_smul_eq_comp_abelJacobi_of_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pts_heckeGenOne_smul_eq_comp_abelJacobi_of_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul (solution)
