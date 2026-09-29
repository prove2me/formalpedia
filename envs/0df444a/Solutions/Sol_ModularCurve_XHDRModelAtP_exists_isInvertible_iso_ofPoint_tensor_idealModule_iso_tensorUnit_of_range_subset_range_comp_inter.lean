-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bd1f9a02-4e71-5191-844d-9f498a1924ce

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_orientedCrossingChart_valuationSubring
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_section_basicOpen_sup_mul_eq_of_mul_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
import Theorems.Thm_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "ModularCurve.XHDRLevel.bcMap_fst ModularCurve.XHDRLevel.bcMap_snd_assoc ModularCurve.XHDRLevel.bcMap_fst_assoc ModularCurve.XHDRLevel.bcMap_snd ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups
open MvPolynomial

namespace R2Kit
variable {p : ℕ}
theorem fix_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (r : XHDRLevel.R p) :
    σ (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) r) = algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) r := by
  rw [IsScalarTower.algebraMap_apply (XHDRLevel.R p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]
theorem specMap_comp_specMap_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact fix_algebraMap σ r
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
theorem subtype_comp_toRingHom (τ : ↥(A.decompositionSubgroup ℚ)) :
    A.subtype.comp (MulSemiringAction.toRingHom _ (↥A) τ) =
      ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype := by
  ext a; rfl
theorem toRingHom_comp_eq (τ : ↥(A.decompositionSubgroup ℚ)) (ρ : XHDRLevel.R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ)) :
    (MulSemiringAction.toRingHom _ (↥A) τ).comp ρ = ρ := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  have h1 := RingHom.congr_fun (subtype_comp_toRingHom τ) (ρ r)
  have h2 := RingHom.congr_fun hρ r
  simp only [RingHom.comp_apply] at h1 h2 ⊢
  rw [show ((MulSemiringAction.toRingHom _ (↥A) τ) (ρ r) : AlgebraicClosure ℚ) = A.subtype ((MulSemiringAction.toRingHom _ (↥A) τ) (ρ r)) from rfl,
    h1, RingHom.coe_coe, show (A.subtype (ρ r)) = algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) r from h2, fix_algebraMap]
  exact h2.symm
end R2Kit

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ))) (hψ : ψ.1 = barPt A)
    (β : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)))
    (hβ : β.1 = resPt A)

    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
      ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫
        pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
    (hy₂ : y ≫ pullback.snd _ _ = 𝟙 _)

    (hc : (Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)

    (ybar₁ ybar₂ : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (hybar₁ : ybar₁.1 = ((𝔛.Meta.pointEquivPlace).symm
      (arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • V)).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hybar₂ : ybar₂.1 = ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p)) :
    ∃ L : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules,
      Scheme.Modules.IsInvertible L ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓM M H) hj) ψ)).obj L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₂.1 ybar₂.2).idealModule) ∧
      (∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L ≅
        𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules)) := by
  classical

  haveI : IsIso 𝔛.eeta := 𝔛.eeta_iso
  haveI hci : ∀ j, IsClosedImmersion (𝔛.comp A hA ρ hρ j) := 𝔛.comp_isClosedImmersion A hA ρ hρ
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  let c := toBase p (ΓM M H) hj
  let tA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom ρ)
  let tκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (R p)) :=
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))
  have hbase : tκ = resPt A ≫ tA := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let B : pullback c tκ ⟶ pullback c tA := baseChangeSnd c β
  have hB₁ : B ≫ pullback.fst _ _ = pullback.fst _ _ := BaseChange.baseChangeSnd_fst' _ _ _
  have hB₂ : B ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [BaseChange.baseChangeSnd_snd', hβ]

  obtain ⟨g₀, hg₀, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    (𝔛.comp A hA ρ hρ 0) y hc.1
  obtain ⟨g₁, hg₁, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    (𝔛.comp A hA ρ hρ 1) y hc.2
  let nκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) :=
    pullback.lift g₀ g₁ (hg₀.trans hg₁.symm)
  let n₀ : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := nκ.base (IsLocalRing.closedPoint _)
  set xn := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ B).base n₀ with hxn
  have hyn : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n₀ =
      y.base (IsLocalRing.closedPoint _) := by
    show ((nκ ≫ pullback.fst _ _ ≫ 𝔛.comp A hA ρ hρ 0).base (IsLocalRing.closedPoint _)) = _
    rw [pullback.lift_fst_assoc, hg₀]

  obtain ⟨e, he, U, hxU, f, hf, hfib, hpt, ⟨Wet, hWet, hEt⟩, hequiv, hor₁, hor₂, hor₃, hor₄⟩ :=
    ModularCurve.XHDRModelAtP.forall_exists_orientedCrossingChart_valuationSubring
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ B hB₁ hB₂ n₀

  let sA : Spec (CommRingCat.of ↥A) ⟶ pullback c tA := pullback.lift s.1 (𝟙 _) (by rw [s.2, Category.id_comp])
  have hsA : sA ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hysA : resPt A ≫ sA = y ≫ B := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hB₁, hy₁]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hB₂, ← Category.assoc, hy₂, Category.id_comp, Category.comp_id]
  have hsn : sA.base (IsLocalRing.closedPoint ↥A) = xn := by
    have h1 : (resPt A ≫ sA).base (IsLocalRing.closedPoint _) = sA.base (IsLocalRing.closedPoint ↥A) := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
    rw [← h1, hysA, Scheme.Hom.comp_apply, ← hyn, hxn, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.mp hσ
  have hτσ' : ((τ : ↥(A.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ := hτσ
  subst hτσ'
  set σA : ↥A →+* ↥A := MulSemiringAction.toRingHom _ (↥A) τ with hσAdef
  have hσAρ : σA.comp ρ = ρ := R2Kit.toRingHom_comp_eq τ ρ hρ

  have hover : (Spec.map (CommRingCat.ofHom σA) ≫ s.1) ≫ c = tA := by
    rw [Category.assoc, s.2]
    show _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσAρ]
  let s₁ : SchemeHomOver tA c := ⟨Spec.map (CommRingCat.ofHom σA) ≫ s.1, hover⟩
  let s₁A : Spec (CommRingCat.of ↥A) ⟶ pullback c tA := pullback.lift s₁.1 (𝟙 _) (by rw [s₁.2, Category.id_comp])
  have hs₁A : s₁A ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

  have hresσ : (IsLocalRing.residue ↥A).comp σA = IsLocalRing.residue ↥A := by
    ext a
    rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, IsLocalRing.ResidueField.residue_smul]
    have h : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥A) τ = 1 :=
      (MonoidHom.mem_ker).mp hτ
    have := RingEquiv.congr_fun h (IsLocalRing.residue (↥A) a)
    simpa [MulSemiringAction.toRingAut_apply] using this
  have hys₁A : resPt A ≫ s₁A = y ≫ B := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hB₁, hy₁]
      show Spec.map _ ≫ Spec.map _ ≫ s.1 = Spec.map _ ≫ s.1
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hresσ]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hB₂, ← Category.assoc, hy₂, Category.id_comp, Category.comp_id]
  have hs₁n : s₁A.base (IsLocalRing.closedPoint ↥A) = xn := by
    have h1 : (resPt A ≫ s₁A).base (IsLocalRing.closedPoint _) = s₁A.base (IsLocalRing.closedPoint ↥A) := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
    rw [← h1, hys₁A, Scheme.Hom.comp_apply, ← hyn, hxn, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

  obtain ⟨x', y', hxy, sU, hx', hy', hsU, hfs⟩ :=
    ModularCurve.XHDRModelAtP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
      p M H hpM hpM2 hj 𝔛 A hA ρ hρ B n₀ e U hxU f hf hfib sA hsA hsn
  obtain ⟨x'', y'', hxy'', sU', -, -, hsU', -⟩ :=
    ModularCurve.XHDRModelAtP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
      p M H hpM hpM2 hj 𝔛 A hA ρ hρ B n₀ e U hxU f hf hfib s₁A hs₁A hs₁n
  clear x'' y'' hxy''
  have hxyσ : σA x' * σA y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e) := by
    rw [← map_mul, hxy, Algebra.algebraMap_self, RingHom.id_apply, map_pow, map_natCast]
  have hsU₂ : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ := by rw [← Category.assoc, hsU, hsA]
  have hsU'₂ : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ := by rw [← Category.assoc, hsU', hs₁A]
  have hsU'₁ : sU' ≫ U.ι ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom σA) ≫ sU ≫ U.ι ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hsU', pullback.lift_fst, ← Category.assoc (sU), hsU, pullback.lift_fst]
  have hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e)
      (σA x') (σA y') hxyσ).toRingHom) :=
    hequiv τ hτ x' y' hxy hxyσ sU sU' hsU₂ hsU'₂ hsU'₁ hfs

  have hx'0 : x' ≠ 0 := by
    intro h0
    rw [h0, zero_mul, Algebra.algebraMap_self, RingHom.id_apply] at hxy
    exact (pow_ne_zero e (by exact_mod_cast (Fact.out : p.Prime).ne_zero :
      ((p : ℕ) : ↥A) ≠ 0)) hxy.symm
  have hτdec : ((τ : ↥(A.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.decompositionSubgroup ℚ := τ.2
  have hx'K : ((x' : ↥A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hx'0 (Subtype.ext h)
  have hval : A.valuation (((σA x' : ↥A) : AlgebraicClosure ℚ) * ((x' : AlgebraicClosure ℚ))⁻¹) = 1 := by
    rw [map_mul, map_inv₀, show ((σA x' : ↥A) : AlgebraicClosure ℚ) =
        ((τ : ↥(A.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x' : AlgebraicClosure ℚ) from rfl,
      ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hτdec, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).mpr hx'K
  have hcA : ((σA x' : ↥A) : AlgebraicClosure ℚ) * ((x' : AlgebraicClosure ℚ))⁻¹ ∈ A := A.mem_of_valuation_le_one _ hval.le
  have hcunit : IsUnit (⟨_, hcA⟩ : ↥A) := (A.valuation_eq_one_iff _).mpr hval
  obtain ⟨w, hw⟩ : ∃ w : (↥A)ˣ, ((w : ↥A) : AlgebraicClosure ℚ) = ((σA x' : ↥A) : AlgebraicClosure ℚ) * ((x' : AlgebraicClosure ℚ))⁻¹ :=
    ⟨hcunit.unit, by rw [IsUnit.unit_spec]⟩
  have hwx : σA x' = (w : ↥A) * x' := by
    apply Subtype.ext
    show ((σA x' : ↥A) : AlgebraicClosure ℚ) = ((w : ↥A) : AlgebraicClosure ℚ) * (x' : AlgebraicClosure ℚ)
    rw [hw, inv_mul_cancel_right₀ hx'K]
  have hwy : (w : ↥A) * σA y' = y' := by
    have h1 : (w : ↥A) * x' * σA y' = x' * y' := by rw [← hwx, hxyσ, hxy]
    have h2 : x' * ((w : ↥A) * σA y') = x' * y' := by rw [← mul_assoc, mul_comm x', h1]
    exact mul_left_cancel₀ hx'0 h2
  have hwy' : σA y' = (↑w⁻¹ : ↥A) * y' := by
    calc σA y' = ((↑w⁻¹ : ↥A) * (w : ↥A)) * σA y' := by rw [Units.inv_mul, one_mul]
      _ = (↑w⁻¹ : ↥A) * y' := by rw [mul_assoc, hwy]

  have hxyt : x' * y' = ((p : ℕ) : ↥A) ^ e := by rw [hxy, Algebra.algebraMap_self, RingHom.id_apply]
  obtain ⟨gM, hga, hgb, hgu⟩ := MvPolynomial.CrossingQuotient.exists_section_basicOpen_sup_mul_eq_of_mul_eq (↥A) _ x' y' hxyt w

  obtain ⟨yU, hyU, hyUW⟩ := hWet
  haveI := hEt
  obtain ⟨-, -, hres⟩ := hpt yU hyU
  have hfY : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) = U.ι ≫ pullback.snd _ _ := hf
  have hbij := AlgebraicGeometry.bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
    (U.ι ≫ pullback.snd c tA) (Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e))))) f hfY yU Wet hyUW hres
  have huniq_gen : ∀ (xx yy : ↥A) (hh : xx * yy = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
      (s₀ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})), s₀ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₀.base (IsLocalRing.closedPoint ↥A)) = xn →
      s₀ ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) xx yy hh).toRingHom) →
      ∀ (s₁' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})), s₁' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₁'.base (IsLocalRing.closedPoint ↥A)) = xn →
      s₁' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) xx yy hh).toRingHom) →
      s₁' = s₀ := by
    intro xx yy hh s₀ hs₀ hs₀x hfs₀ s₁' hs₁' hs₁'x hfs₁'
    have hpt₀ : s₀.base (IsLocalRing.closedPoint ↥A) = yU := by
      apply U.ι.isOpenEmbedding.injective
      rw [hs₀x, hyU]
    have hpt₁ : s₁'.base (IsLocalRing.closedPoint ↥A) = yU := by
      apply U.ι.isOpenEmbedding.injective
      rw [hs₁'x, hyU]
    have := hbij.1 (a₁ := ⟨s₁', hs₁', hpt₁⟩) (a₂ := ⟨s₀, hs₀, hpt₀⟩) (Subtype.ext (by
      show s₁' ≫ f = s₀ ≫ f
      rw [hfs₁', hfs₀]))
    exact congrArg Subtype.val this
  have huniq := fun s₂ (h₁ : s₂ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (h₂ : U.ι.base (s₂.base (IsLocalRing.closedPoint ↥A)) = xn) h₃ =>
    huniq_gen x' y' hxy sU hsU₂ (by rw [← Scheme.Hom.comp_apply, hsU, hsn]) hfs s₂ h₁ h₂ h₃
  have huniq' := fun s₂ (h₁ : s₂ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (h₂ : U.ι.base (s₂.base (IsLocalRing.closedPoint ↥A)) = xn) h₃ =>
    huniq_gen (σA x') (σA y') hxyσ sU' hsU'₂ (by rw [← Scheme.Hom.comp_apply, hsU', hs₁n]) hfs' s₂ h₁ h₂ h₃
  obtain ⟨W₂, W₃, hcov, hW₂U, hxW₂, hW₃, hfO⟩ :=
    ModularCurve.XHDRModelAtP.exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
      p M H hpM hpM2 hj 𝔛 A hA ρ hρ B n₀ e U hxU f hf hfib Wet ⟨yU, hyU, hyUW⟩ x' y' hxy (σA x') (σA y') hxyσ sU sU'
      hsU₂ hsU'₂ (by rw [← Scheme.Hom.comp_apply, hsU, hsn]) (by rw [← Scheme.Hom.comp_apply, hsU', hs₁n]) hfs hfs' huniq huniq'

  let Q := CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)
  let Mdl : Scheme.{0} := CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)
  let φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q x')
  let b : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - CrossingQuotient.V _)
  let aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q ((w : ↥A) * x'))
  let bw : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - algebraMap ↥A Q (w : ↥A) * CrossingQuotient.V _)
  let a' : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q (σA x'))
  let b' : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q (σA y') - CrossingQuotient.V _)
  let O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)
  have haw : a' = aw := by
    show φ _ = φ _
    rw [hwx]
  have hbw : bw = φ (algebraMap ↥A Q (w : ↥A)) * b' := by
    show φ _ = φ _ * φ _
    rw [← map_mul, hwy', mul_sub, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have hDb : Mdl.basicOpen bw = Mdl.basicOpen b' := by
    have hu : IsUnit (φ (algebraMap ↥A Q (w : ↥A))) := ((Units.isUnit w).map _).map _
    rw [hbw, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit (X := Mdl) hu, top_inf_eq]

  let gO : Γ(Mdl, O) := Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM
  have hgO : IsUnit gO := hgu
  let gU : Γ(U, f ⁻¹ᵁ O) := f.app O gO
  have hgUu : IsUnit gU := hgO.map _
  let gX : Γ(pullback c tA, U.ι ''ᵁ (f ⁻¹ᵁ O)) := (U.ι.appIso (f ⁻¹ᵁ O)).inv gU
  have hgXu : IsUnit gX := hgUu.map _
  have hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O) := by
    intro z hz
    let yz : ↥(U : Scheme.{0}) := ⟨z, hW₂U hz.1⟩
    have hyz : U.ι.base yz = z := rfl
    have hmem := hfO yz (by rw [hyz]; exact hz.1) (by rw [hyz]; exact hz.2)
    refine ⟨yz, ?_, hyz⟩
    show f.base yz ∈ O
    refine ⟨hmem.1, ?_⟩
    have h2 : f.base yz ∈ Mdl.basicOpen a' ⊔ Mdl.basicOpen b' := hmem.2
    rw [haw, ← hDb] at h2
    exact h2
  let t : Γ(pullback c tA, W₂ ⊓ W₃) := (pullback c tA).presheaf.map (homOfLE hle).op gX
  have ht : IsUnit t := hgXu.map _

  obtain ⟨L, aL, bL, haL, hbL, htr⟩ := AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_isUnit W₂ W₃ t ht
  have hL : Scheme.Modules.IsInvertible L :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top haL hbL hcov
  refine ⟨L, hL, ?_, ?_⟩
  ·
    have hsW : sU.base (IsLocalRing.closedPoint ↥A) ∈ Wet := by
      have : sU.base (IsLocalRing.closedPoint ↥A) = yU := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hsU, hsn, hyU]
      rw [this]; exact hyUW
    have hsW' : sU'.base (IsLocalRing.closedPoint ↥A) ∈ Wet := by
      have : sU'.base (IsLocalRing.closedPoint ↥A) = yU := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hsU', hs₁n, hyU]
      rw [this]; exact hyUW
    have hbar : barPt A ≫ tA = genPt p := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
    have hP₂ : graphOver c ybar₂.1 ybar₂.2 ≫ baseChangeSnd c ψ = barPt A ≫ sU ≫ U.ι := by
      rw [hsU]
      apply pullback.hom_ext
      · rw [Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, pullback.lift_fst]
        simp only [graphOver, pullback.lift_fst]
        rw [hybar₂, ← hs]
      · rw [Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, pullback.lift_snd, Category.comp_id, hψ]
        simp only [graphOver, pullback.lift_snd_assoc, Category.id_comp]

    have hPbase : ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ toBase p (ΓM M H) hj =
          Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
      rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, ((𝔛.Meta.pointEquivPlace).symm V).2, Category.id_comp]
    have hq : (Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
      rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, hPbase]
      exact R2Kit.specMap_comp_specMap_algebraMap _
    let xσ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
      ⟨pullback.lift _ _ hq ≫ inv 𝔛.eeta, by
        have h1 : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
          rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
        rw [Category.assoc, h1, pullback.lift_snd]⟩
    have hxσ : xσ.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
      show (pullback.lift _ _ hq ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
    have hgal := 𝔛.hgal (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((𝔛.Meta.pointEquivPlace).symm V) xσ hxσ
    have hxσ' : xσ = (𝔛.Meta.pointEquivPlace).symm
        (arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • V) := by
      rw [Equiv.eq_symm_apply, hgal, Equiv.apply_symm_apply]
    have e1 : barPt A ≫ Spec.map (CommRingCat.ofHom σA) =
        Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, R2Kit.subtype_comp_toRingHom]
    have hP₁ : graphOver c ybar₁.1 ybar₁.2 ≫ baseChangeSnd c ψ = barPt A ≫ sU' ≫ U.ι := by
      rw [hsU']
      apply pullback.hom_ext
      · rw [Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, pullback.lift_fst]
        simp only [graphOver, pullback.lift_fst]
        rw [hybar₁, ← hxσ']
        show xσ.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = barPt A ≫ Spec.map (CommRingCat.ofHom σA) ≫ s.1
        rw [hxσ, ← Category.assoc (barPt A), e1, Category.assoc]
        show _ = _ ≫ Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1
        rw [hs]
      · rw [Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, pullback.lift_snd, Category.comp_id, hψ]
        simp only [graphOver, pullback.lift_snd_assoc, Category.id_comp]
    have hxyw : ((w : ↥A) * x') * ((↑w⁻¹ : ↥A) * y') = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e) := by
      rw [← hwx, ← hwy', hxyσ]
    have hlift : (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) (σA x') (σA y') hxyσ) =
        CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) ((w : ↥A) * x') ((↑w⁻¹ : ↥A) * y') hxyw := by
      apply CrossingQuotient.algHom_ext_chart
      · rw [CrossingQuotient.lift_U, CrossingQuotient.lift_U, hwx]
      · rw [CrossingQuotient.lift_V, CrossingQuotient.lift_V, hwy']
    have hfs'w : sU' ≫ f = Spec.map (CommRingCat.ofHom
        (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) ((w : ↥A) * x') ((↑w⁻¹ : ↥A) * y') hxyw).toRingHom) := by
      rw [hfs', hlift]
    haveI := hEt
    exact ModularCurve.XHDRModelAtP.nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ ψ hψ ybar₁ ybar₂ e he U f hf Wet sU sU' hsU₂ hsU'₂ hsW hsW' hP₂ hP₁
      x' y' hxyt hx' hy' w hxyw hxy hfs hfs'w
      (fun h => huniq sU' hsU'₂ (by rw [← Scheme.Hom.comp_apply, hsU', hs₁n]) (h.trans hfs))
      gM hga hgb hgu W₂ W₃ hcov hW₂U hle hW₃ L aL bL haL hbL htr
  · exact ModularCurve.XHDRModelAtP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ B hB₁ hB₂ e he U f hf hor₃ hor₄ x' y' hxyt hx' hy' w gM hga hgb W₂ W₃ hcov hW₂U hle
      L aL bL haL hbL htr

end S_ModularCurve_XHDRModelAtP_exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter (solution)
