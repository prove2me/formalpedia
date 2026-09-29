-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ord_residue_nonneg_of_mem_integers_of_isAffinePlace_of_forall_reduce_eq_ord_nonneg_of_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/de94198e-97c8-5b22-bc4a-fcb334f9c5af

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_mem_integers_of_isAffinePlace_of_forall_reduce_eq_ord_nonneg_of_prolongationDatum
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper"
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply ModularCurve.XHDRLevel.bcMap_fst ModularCurve.XHDRLevel.bcMap_snd_assoc ModularCurve.XHDRLevel.bcMap_fst_assoc ModularCurve.XHDRLevel.bcMap_snd ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace W2Skel

open AlgebraicCurve

section ord
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_nonneg_of_hasValue (v : Place K F) {f : F} {a : K} (h : v.HasValue f a) : 0 ≤ v.ord f :=
  ord_nonneg_of_mem v h.mem

end ord

theorem coe_residue_mul_coeffMap_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers)
    (x' y' : LaurentSeries ↥A)
    (hx' : coeffMap A.subtype x' ∈ xHFunctionFieldBar M H) (hy' : coeffMap A.subtype y' ∈ xHFunctionFieldBar M H)
    (hfy : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x') :
    ((Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
        coeffMap (IsLocalRing.residue ↥A) y' = coeffMap (IsLocalRing.residue ↥A) x' := by
  obtain ⟨hyO, hyres⟩ := Rpd.residue₁_coeffMap y' hy'
  obtain ⟨hxO, hxres⟩ := Rpd.residue₁_coeffMap x' hx'
  have hmul : (⟨f, h₁⟩ : Rpd.R₁.integers) * ⟨⟨coeffMap A.subtype y', hy'⟩, hyO⟩ = ⟨⟨coeffMap A.subtype x', hx'⟩, hxO⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hfy
  have h := congrArg (fun z => ((Rpd.R₁.residue z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :
      LaurentSeries (ResidueField ↥A))) hmul
  simp only [map_mul] at h
  rw [← hyres, ← hxres]
  simpa using h

theorem exists_presentation
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι)
      (yv : ι → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : ι → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : ∀ j, barPt A ≫ (u j).1 = (yv j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : ι → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
      (_ : ∀ j, uκ j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u j).1)
      (_ : ∀ j, uκ j ≫ pullback.snd _ _ = 𝟙 _)
      (n : ι → ℤ) (_ : ∀ j, n j = (𝔛.Meta.pointEquivPlace (yv j)).ord f),
      ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord f = (∑ j, Finsupp.single (𝔛.Meta.pointEquivPlace (yv j)) (n j)) V := by
  classical
  have hco := (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := hco.toHasPrincipalDivisors
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
  let yv : ↥D.support → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
    fun j => 𝔛.Meta.pointEquivPlace.symm j.1
  have hsec := fun j : ↥D.support =>
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq p M H hpM hj 𝔛 A hA ρ hρ (yv j)
  choose u hu uκ huκ₁ huκ₂ _i _P0 _hP0 using hsec
  have hyv : ∀ j : ↥D.support, 𝔛.Meta.pointEquivPlace (yv j) = j.1 := fun j => Equiv.apply_symm_apply _ _
  refine ⟨↥D.support, inferInstance, yv, u, hu, uκ, huκ₁, huκ₂, fun j => D j.1, fun j => by show D j.1 = _; rw [hyv j]; exact hD j.1, fun V => ?_⟩
  simp only [hyv]
  rw [← hD V]
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, ← Finset.sum_coe_sort D.support]

theorem fst_node
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord f)
    (hres : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hss : v ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    0 ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩) := by
  have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (ΓN p M H hpM)
  have hv : v ∈ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p '' ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
    rw [himg]; exact hss
  obtain ⟨y, hy, hyv⟩ := hv
  have hs : (v, y) ∈ SS := by
    rw [hSS, mem_ssNodePairsQExp_iff]
    exact ⟨hy, hyv.symm⟩
  have key := ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp f h₁ h₂ (v, y) hs (fun V hV _ => hreg V hV)
  obtain ⟨c, hc1, -⟩ := key
  exact ord_nonneg_of_hasValue _ hc1

theorem snd_node
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = w → 0 ≤ V.ord f)
    (hres : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hss : w ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    0 ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by
  have hs : (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w, w) ∈ SS := by
    rw [hSS]; exact frob_mk_mem_ssNodePairsQExp hss
  have key := ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp f h₁ h₂ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w, w) hs (fun V _ hV => hreg V hV)
  obtain ⟨c, -, hc2⟩ := key
  exact ord_nonneg_of_hasValue _ hc2

theorem fst_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord f)
    (hres : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hss : v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    0 ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩) := by
  classical
  have hgc := (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp Rpd f).mp h₁
  obtain ⟨x0, y0, hybar, hfxy⟩ := hgc
  have hmw := ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA f x0 y0 hybar hfxy
  obtain ⟨x', y', hx'mem, hy'mem, hy'bar, hfxy'⟩ := hmw
  have hg : ((Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' :=
    coe_residue_mul_coeffMap_eq p M H hpM A θ Psp Rpd f h₁ x' y' hx'mem hy'mem hfxy'
  have hx'bar : coeffMap (IsLocalRing.residue ↥A) x' ≠ 0 := by
    intro h0
    rw [h0] at hg
    rcases mul_eq_zero.mp hg with hg0 | hy0
    · exact hres (by exact_mod_cast hg0)
    · exact hy'bar hy0

  obtain ⟨Pbar, hPbar⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 v

  have hf0 : f ≠ 0 := by
    intro hf
    apply hres
    have hz : (⟨f, h₁⟩ : Rpd.R₁.integers) = 0 := Subtype.ext hf
    rw [hz, map_zero]
  have hpres := exists_presentation p M H hpM hj 𝔛 A hA ρ hρ f hf0
  obtain ⟨ι, _inst, yv, u, hu, uκ, huκ₁, huκ₂, n, hn, hdiv⟩ := hpres
  have key := ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
    p M hpM hpM2 H hHp A hA hj 𝔛 ρ hρ f x' y' hx'bar hy'bar hfxy' (Rpd.R₁.residue ⟨f, h₁⟩) hg yv u hu uκ huκ₁ huκ₂ n hdiv Pbar
    (by rw [hPbar]; exact hss)
  rw [hPbar] at key
  rw [key]
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases hjc : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Pbar.1 = (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥A))
  · rw [if_pos hjc]
    have hc := hcomp 0 (yv j) (u j) (hu j) (uκ j) (huκ₁ j) (huκ₂ j) Pbar hjc
    rw [if_pos rfl, hPbar] at hc
    have h := hreg (𝔛.Meta.pointEquivPlace (yv j)) hc.symm
    rw [← hn j] at h
    exact h
  · rw [if_neg hjc]

theorem snd_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = w → 0 ≤ V.ord f)
    (hres : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hss : w ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    0 ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by
  classical
  have hθ₁ : θ f ∈ Rpd.R₁.integers := (Rpd.mem_integers₂_iff f).mp h₂
  have hres₂ : Rpd.R₂.residue ⟨f, h₂⟩ = Rpd.R₁.residue ⟨θ f, hθ₁⟩ := Rpd.residue₂_eq f h₂
  have hgc := (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp Rpd (θ f)).mp hθ₁
  obtain ⟨x0, y0, hybar, hfxy⟩ := hgc
  have hmw := ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (θ f) x0 y0 hybar hfxy
  obtain ⟨x', y', hx'mem, hy'mem, hy'bar, hfxy'⟩ := hmw
  have hg : ((Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' =
      coeffMap (IsLocalRing.residue ↥A) x' := by
    rw [hres₂]
    exact coe_residue_mul_coeffMap_eq p M H hpM A θ Psp Rpd (θ f) hθ₁ x' y' hx'mem hy'mem hfxy'
  have hx'bar : coeffMap (IsLocalRing.residue ↥A) x' ≠ 0 := by
    intro h0
    rw [h0] at hg
    rcases mul_eq_zero.mp hg with hg0 | hy0
    · exact hres (by exact_mod_cast hg0)
    · exact hy'bar hy0

  obtain ⟨Pbar, hPbar⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 w

  have hf0 : f ≠ 0 := by
    intro hf
    apply hres
    have hz : (⟨f, h₂⟩ : Rpd.R₂.integers) = 0 := Subtype.ext hf
    rw [hz, map_zero]
  have hpres := exists_presentation p M H hpM hj 𝔛 A hA ρ hρ f hf0
  obtain ⟨ι, _inst, yv, u, hu, uκ, huκ₁, huκ₂, n, hn, hdiv⟩ := hpres
  have key := ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
    p M hpM hpM2 H hHp A hA hj 𝔛 ρ hρ θ hwgen f x' y' hx'bar hy'bar hfxy' (Rpd.R₂.residue ⟨f, h₂⟩) hg yv u hu uκ huκ₁ huκ₂ n hdiv Pbar
    (by rw [hPbar]; exact hss)
  rw [hPbar] at key
  rw [key]
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases hjc : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Pbar.1 = (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥A))
  · rw [if_pos hjc]
    have hc := hcomp 1 (yv j) (u j) (hu j) (uκ j) (huκ₁ j) (huκ₂ j) Pbar hjc
    rw [if_neg (by decide), hPbar] at hc
    have h := hreg (𝔛.Meta.pointEquivPlace (yv j)) hc.symm
    rw [← hn j] at h
    exact h
  · rw [if_neg hjc]

theorem clause_fst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))  :
    (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
        (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord f) →
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩)) := by
  intro f h₁ h₂ v _haff hreg hres
  by_cases hss : v ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p
  · exact fst_node p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx f h₁ h₂ v hreg hres hss
  · exact fst_smooth p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx f h₁ h₂ v hreg hres hss

theorem clause_snd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))  :
    (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
        (u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A u →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = u → 0 ≤ V.ord f) →
      Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ u.ord (Rpd.R₂.residue ⟨f, h₂⟩)) := by
  intro f h₁ h₂ w _haff hreg hres
  by_cases hss : w ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p
  · exact snd_node p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx f h₁ h₂ w hreg hres hss
  · exact snd_smooth p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx f h₁ h₂ w hreg hres hss

end W2Skel

open W2Skel

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
        (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord f) →
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩)) ∧

    (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
        (u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A u →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = u → 0 ≤ V.ord f) →
      Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ u.ord (Rpd.R₂.residue ⟨f, h₂⟩)) :=
  ⟨W2Skel.clause_fst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx, W2Skel.clause_snd p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ hwgen α hα hβ hα_coe Psp Rpd hcomp x hx⟩

end S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_mem_integers_of_isAffinePlace_of_forall_reduce_eq_ord_nonneg_of_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_mem_integers_of_isAffinePlace_of_forall_reduce_eq_ord_nonneg_of_prolongationDatum (solution)
