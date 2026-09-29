-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d51f45f9-83cc-59a4-b279-685e91b4f4ec

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.XHDRLevel.bcMap_fst ModularCurve.XHDRLevel.bcMap_snd_assoc ModularCurve.XHDRLevel.bcMap_fst_assoc ModularCurve.XHDRLevel.bcMap_snd ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)

namespace F2aAux
open ModularCurve

theorem placeOfPoint_ne_placeOn_of_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ (if i = 0 then 𝔛.placeOn0 A hA ρ hρ n else 𝔛.placeOn1 A hA ρ hρ n) := by

  have hsm : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [← Scheme.Hom.comp_apply, huκ₁, Scheme.Hom.comp_apply]
    exact husm ⟨_, rfl⟩
  have hnot := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).1 hsm
  rw [← hP] at hnot
  obtain ⟨⟨hb, hbpl⟩, ⟨ha, hapl⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hinvE : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hcond : (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) =
      (𝔛.comp A hA ρ hρ 1).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
    have := congrArg (fun f => f.base n) (pullback.condition (f := 𝔛.comp A hA ρ hρ 0) (g := 𝔛.comp A hA ρ hρ 1))
    simpa only [Scheme.Hom.comp_apply] using this
  intro heq
  apply hnot
  fin_cases i
  ·
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, ha⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hapl.symm)
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, hcond]
    exact ⟨_, rfl⟩
  ·
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, hb⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hbpl.symm)
    refine ⟨?_, ⟨_, rfl⟩⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, ← hcond]
    exact ⟨_, rfl⟩

end F2aAux

theorem plumb_Dvz (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Dv D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (h : ↥(ModularCurve.xHFunctionFieldBar M H)) (hh : h ≠ 0)
    (hDvD : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
        (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h) :
    AlgebraicCurve.Pic0.mk Dv = AlgebraicCurve.Pic0.mk D' := by
  unfold AlgebraicCurve.Pic0.mk
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AlgebraicCurve.Divisor.mem_principal]
  refine ⟨h⁻¹, inv_ne_zero hh, fun v => ?_⟩
  rw [AlgebraicCurve.Place.ord_inv, AddMemClass.coe_add, NegMemClass.coe_neg, Finsupp.add_apply, Finsupp.neg_apply, hDvD v]
  ring

set_option maxHeartbeats 3200000 in
open ModularCurve in

theorem plumb_admissible
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (k : ℕ) (c : Fin k → Fin 2)
    (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (husm : ∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
    (huκ₁ : ∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1)
    (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (hP : ∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl)))
    (n : Fin k → ℤ)
    (hn₀ : ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0)
    (hn₁ : ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0) :
    ∃ xg : ↥(GluingData.admissible O.ssFinset),
      ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ∧
      ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).2.1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ∧
      ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).2.2 = 0) := by
  classical
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩

  haveI hCO : AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (𝔛.Mfib Pl hPl ρ hρ).toBase (𝔛.Mfib Pl hPl ρ hρ).ffEquiv (𝔛.Mfib Pl hPl ρ hρ).ffEquiv_algebraMap
  have hdegF : ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)), v.deg = 1 := fun v => by
    haveI := AlgebraicCurve.IsCurveOver.finiteResidue (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2

  have hdegsum : ∀ j : Fin 2, AlgebraicCurve.Divisor.degree (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
      (∑ i ∈ Finset.univ.filter (fun i => c i = j), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) (1 : ℤ)) =
      ∑ i ∈ Finset.univ.filter (fun i => c i = j), n i := fun j => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, AlgebraicCurve.Divisor.degree_single, hdegF, Nat.cast_one, mul_one, smul_eq_mul, mul_one]

  have hoffSS : ∀ (i : Fin k) (s : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), s ∈ O.ssFinset →
      (c i = 0 → (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i) ≠ s.1) ∧ (c i = 1 → (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i) ≠ s.2) := by
    intro i s hs
    have hs' := (O.mem_ssFinset_iff s).1 hs
    rw [ModularCurve.mem_ssNodePairsQExp_iff] at hs'
    obtain ⟨hy, hs1⟩ := hs'
    have hoff := F2aAux.placeOfPoint_ne_placeOn_of_smooth p M H hpM hpM2 hj 𝔛 Pl hPl ρ hρ (c i) (u i) (husm i) (uκ i) (huκ₁ i) (P i) (hP i)
      ((𝔛.nodeEquiv Pl hPl ρ hρ).symm ⟨s.2, hy⟩)
    constructor
    · intro hc
      rw [hc] at hoff
      simpa only [Fin.isValue, ↓reduceIte, ModularCurve.XHDRModelAtP.placeOn0, Equiv.apply_symm_apply, ← hs1] using hoff
    · intro hc
      rw [hc] at hoff
      simpa only [Fin.isValue, one_ne_zero, ↓reduceIte, ModularCurve.XHDRModelAtP.placeOn1, Equiv.apply_symm_apply] using hoff
  have hvan : ∀ (j : Fin 2) (w : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))),
      (∀ i, c i = j → (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i) ≠ w) →
      (∑ i ∈ Finset.univ.filter (fun i => c i = j), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) (1 : ℤ)) w = 0 := by
    intro j w hw
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (hw i hi.2), smul_zero]
  have hmem₀ : (∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) (1 : ℤ)) ∈
      AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) := by
    rw [AlgebraicCurve.Divisor.mem_degZero, hdegsum, hn₀]
  have hmem₁ : (∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) (1 : ℤ)) ∈
      AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) := by
    rw [AlgebraicCurve.Divisor.mem_degZero, hdegsum, hn₁]
  refine ⟨⟨⟨_, _, 0⟩, hmem₀, hmem₁, fun s hs => ⟨?_, ?_⟩⟩, rfl, rfl, rfl⟩
  · exact hvan 0 s.1 fun i hi => (hoffSS i s hs).1 hi
  · exact hvan 1 s.2 fun i hi => (hoffSS i s hs).2 hi

set_option maxHeartbeats 3200000 in
open ModularCurve in

theorem plumb_E
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (k : ℕ) (c : Fin k → Fin 2) (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C) (n : Fin k → ℤ)
    (g hbar : Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (hg0 : g ≠ 0) (hhbar0 : hbar ≠ 0)
    (hord : ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      v.ord (g * hbar ^ p) =
        (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
          n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) v)
    (xg : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 =
      ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) :
    ∃ E : AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      AlgebraicCurve.Pic0.mk E =
        (AlgebraicCurve.GluedPic0.toPic0Pair O.ssFinset (AlgebraicCurve.GluedPic0.mk O.ssFinset xg)).1 ∧
      ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
        (p : ℤ) * (E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))) v = v.ord g := by
  classical
  obtain ⟨hPD, -, -⟩ := ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
    p M H hpM hpM2 (IsLocalRing.ResidueField ↥Pl)
  haveI := hPD
  obtain ⟨Dh, hDh, hDhdeg⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := IsLocalRing.ResidueField ↥Pl) hbar hhbar0
  have hx1deg : (xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 ∈
      AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) := xg.2.1
  have hEdeg : (xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 - Dh ∈
      AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) := by
    rw [AlgebraicCurve.Divisor.mem_degZero, map_sub, hDhdeg, sub_zero]
    exact AlgebraicCurve.Divisor.mem_degZero.mp hx1deg
  refine ⟨⟨_, hEdeg⟩, ?_, fun v => ?_⟩
  · rw [AlgebraicCurve.GluedPic0.toPic0Pair_mk]
    unfold AlgebraicCurve.Pic0.mk
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AlgebraicCurve.Divisor.mem_principal]
    refine ⟨hbar, hhbar0, fun w => ?_⟩
    rw [AddMemClass.coe_add, NegMemClass.coe_neg, Finsupp.add_apply, Finsupp.neg_apply]
    show -(((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 - Dh) w) + _ = _
    rw [Finsupp.sub_apply, hDh w]
    show -(((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1) w - w.ord hbar) +
      ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1) w = w.ord hbar
    ring
  · have h1 := hord v
    rw [AlgebraicCurve.Place.ord_mul _ hg0 (pow_ne_zero _ hhbar0), ← zpow_natCast, AlgebraicCurve.Place.ord_zpow, ← hx₁] at h1
    show (p : ℤ) * (((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 - Dh) v) = v.ord g
    rw [Finsupp.sub_apply, hDh v]
    linarith

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open ModularCurve in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (hp2 : p ≠ 2)
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)

    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type)
    [CommRing R]
    [IsDomain R]
    [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]

    [Algebra R (AlgebraicClosure ℚ)]
    [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R)
    (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ}
    (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (Wbar : ModularCurve.JH M H →+ ModularCurve.JH M H)
    (hWbar : ∀ x : ModularCurve.JH M H, Wbar x = wgen • x)
    :
    ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∈ O.finPts p →
      ∀ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) → f ≠ 0 →
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) →
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y →
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
      ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl),
        (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y →
      (∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          (p : ℤ) ∣ v.ord g) →
      ∃ (k : ℕ) (c : Fin k → Fin 2)
        (y : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
        (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
        (n : Fin k → ℤ)
        (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
        (xg : ↥(GluingData.admissible O.ssFinset))
        (E : AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))),

        (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (y i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
        (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
        (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
        (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
        (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧

        (∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0) ∧
        (∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0) ∧

        ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
          ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (y i)) 1) ∧
        ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).1 =
          ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ∧
        ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).2.1 =
          ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ∧
        ((xg : GluingData (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) O.ssFinset).2.2 = 0) ∧
        AlgebraicCurve.Pic0.mk Dv = Wbar ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧

        AlgebraicCurve.Pic0.mk E =
          (AlgebraicCurve.GluedPic0.toPic0Pair O.ssFinset (AlgebraicCurve.GluedPic0.mk O.ssFinset xg)).1 ∧
        ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          (p : ℤ) * (E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))) v = v.ord g := by
  intro x hx D f y hDx hf hdiv hfy hy g hg hpg
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩

  have hW := ModularCurve.JHNeronObjectAtP.wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree
      p hp2 M hpM hpM2 H hHp S hin Pl hPl hj 𝔛 Λ hrepΛ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂
      hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ R hRA hRdvr hRirr hRfix hRmax 𝒢 Δ hΔinj hΔlev hΔgal hΔhecke wgen hwgen ρ hρ hσA hsp
      Wbar hWbar p _ hx

  have hext := ((ModularCurve.JHNeronObjectAtP.mem_finPts_iff p M H hpM Pl hPl Λ O p _).mp hW).2

  have hpz : p • Wbar (x : ModularCurve.JH M H) = 0 := by
    have h1 : p • ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact AlgebraicCurve.Pic0.mem_torsion.mp x.2
    rw [← map_nsmul, h1, map_zero]

  have hD'z : AlgebraicCurve.Pic0.mk (SemilinearAut.degZeroSMulHom wgen D) = Wbar (x : ModularCurve.JH M H) := by
    rw [hWbar, ← hDx]
    rfl
  have hdiv' : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * ((SemilinearAut.degZeroSMulHom wgen D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(ModularCurve.xHFunctionFieldBar M H))) : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
        v.ord f := fun v => by
    rw [SemilinearAut.coe_degZeroSMulHom]
    exact hdiv v

  obtain ⟨h, xh, yh, hbar, k, c, yv, u, uκ, P, n, Dv, hh, hxh, hyh, hhw, hhbar, hu, husm, huκ₁, huκ₂, hP, hn₀, hn₁, hDv, hDvD, hord⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 Λ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over
      hεbar hεbar_aj hpts_law hAJ ρ hρ hσA _ hext hpz _ hD'z f hf hdiv' y hfy hy g hg

  obtain ⟨xg, hx₁, hx₂, hx₃⟩ := plumb_admissible p M hpM hpM2 H Pl hPl hj 𝔛 Λ O ρ hρ k c u husm uκ huκ₁ P hP n hn₀ hn₁
  have hg0 : g ≠ 0 := by
    intro h0
    apply hy
    rw [← hg, h0]
    rfl
  have hhbar0 : hbar ≠ 0 := by
    intro h0
    apply hxh
    rw [← hhbar, h0]
    simp
  obtain ⟨E, hEcls, hpE⟩ := plumb_E p M hpM hpM2 H Pl hPl hj 𝔛 Λ O ρ hρ k c P n g hbar hg0 hhbar0 hord xg hx₁
  refine ⟨k, c, yv, u, uκ, P, n, Dv, xg, E, hu, husm, huκ₁, huκ₂, hP, hn₀, hn₁, hDv, hx₁, hx₂, hx₃, ?_, hEcls, hpE⟩
  rw [← hD'z]
  exact plumb_Dvz M H Dv _ h hh hDvD

end S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree (solution)
