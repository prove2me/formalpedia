-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.AuxLevel.formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/0e7939c7-8584-54b1-9bdf-ea920cf10848

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
import Theorems.Thm_Algebra_FormallySmooth_residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_Algebra_Smooth_isIntegrallyClosed_of_isDomain
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_div_two_of_eq_closure_isLevelAutAt_gamma_of_eq_two_of_dvd
import Theorems.Thm_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
import Theorems.Thm_ModularCurve_FullLevel_Diamond_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_linkedScalars_of_eq_two_of_dvd
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.LevelModuliDatum.Twist.instCommRing ModularCurve.LevelModuliDatum.Twist.instAlgebra ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd"
p2m_attr_erase "instance" "KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.LevelModuliPackageAbs.instCommRing ModularCurve.LevelModuliPackageAbs.instAlgebra ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.instIsElliptic_tateBase ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.mk.injEq WeierstrassCurve.DrinfeldGlobal.DrinfeldTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.mk.sizeOf_spec WeierstrassCurve.DrinfeldGlobal.DrinfeldTransport.mk.sizeOf_spec AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq ModularCurve.LevelComponent.mk.sizeOf_spec ModularCurve.LevelComponent.mk.injEq ModularCurve.LevelComponent.Raw.mk.injEq ModularCurve.LevelComponent.Raw.mk.sizeOf_spec ModularCurve.RigidWeierstrassData.mk.sizeOf_spec ModularCurve.RigidWeierstrassData.mk.injEq ModularCurve.LevelModuliPackage.mk.sizeOf_spec ModularCurve.LevelModuliDatum.mk.sizeOf_spec ModularCurve.LevelModuliDatum.SemilinearProblemAut.mk.injEq ModularCurve.LevelModuliDatum.SemilinearProblemAut.mk.sizeOf_spec ModularCurve.LevelModuliDatum.ProblemAut.mk.sizeOf_spec ModularCurve.LevelModuliPackage.mk.injEq ModularCurve.LevelModuliDatum.ProblemAut.mk.injEq ModularCurve.LevelModuliDatum.mk.injEq ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal ModularCurve.LevelModuliPackageAbs.mk.sizeOf_spec ModularCurve.LevelModuliPackageAbs.mk.injEq ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U"
p2m_attr_erase "simp" "CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3GlueKit

open IsLocalRing

variable {K L : Type*} [Field K] [Field L]

def comapEquiv (e : K ≃+* L) (V : ValuationSubring L) : (V.comap (e : K →+* L)) ≃+* V where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by show e (e.symm y) ∈ V; rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_comapEquiv (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    ((comapEquiv e V x : V) : L) = e x := rfl

theorem isDiscreteValuationRing_comap (e : K ≃+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap (e : K →+* L)) :=
  let f := (comapEquiv e V).symm
  { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective f.toRingHom f.surjective
    toIsLocalRing := inferInstance
    not_a_field' := by
      intro h
      apply IsDiscreteValuationRing.not_a_field (R := V)
      rw [eq_bot_iff] at h ⊢
      intro y hy
      have : f y ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
        exact fun hu => hy (by simpa using hu.map f.symm.toRingHom)
      have := h this
      rw [Ideal.mem_bot] at this ⊢
      simpa using congrArg f.symm this }

theorem mem_maximalIdeal_comap_iff (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    x ∈ maximalIdeal (V.comap (e : K →+* L)) ↔ (comapEquiv e V x) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => by simpa using h.map (comapEquiv e V).toRingHom,
    fun h => by simpa using h.map (comapEquiv e V).symm.toRingHom⟩

theorem maximalIdeal_comap_eq_span (e : K ≃+* L) (V : ValuationSubring L) (π : V)
    (h : maximalIdeal V = Ideal.span {π}) :
    maximalIdeal (V.comap (e : K →+* L)) = Ideal.span {(comapEquiv e V).symm π} := by
  apply le_antisymm
  · intro x hx
    rw [mem_maximalIdeal_comap_iff, h, Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(comapEquiv e V).symm c, ?_⟩
    apply (comapEquiv e V).injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hc
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_comap_iff,
      RingEquiv.apply_symm_apply, h]
    exact Ideal.mem_span_singleton_self π

theorem exists_subring_image {R S : Type*} [Ring R] [Ring S] (s : Subring R) (f : R →+* S) :
    ∃ B : Subring S, ∀ y : S, y ∈ B ↔ ∃ x : R, x ∈ s ∧ y = f x :=
  ⟨s.map f, fun y => by
    rw [Subring.mem_map]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩⟩

theorem exists_namingBlock {k E : Type*} [Field k] [Field E] [Algebra k E]
    (O : Type*) [CommRing O] [Algebra O E] [Algebra O k] [IsScalarTower O k E]
    (S : Set (E ≃ₐ[k] E)) (Bt : Subalgebra O E) (Wt : ValuationSubring E) :
    ∃ (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (B₀ : Subalgebra O E) (W₀' : ValuationSubring K₀),
      G = Subgroup.closure S ∧ K₀ = IntermediateField.fixedField G ∧
      (∀ f : E, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ G → τ f = f) ∧
      (∀ f : K₀, f ∈ W₀' ↔ ((f : E)) ∈ Wt) := by
  refine ⟨Subgroup.closure S, IntermediateField.fixedField (Subgroup.closure S),
    { carrier := {f : E | f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.closure S → τ f = f}
      mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, algebraMap_mem' := ?_ },
    Wt.comap (algebraMap _ E), rfl, rfl, fun f => Iff.rfl, fun f => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.mul_mem ha hb, fun τ hτ => by rw [map_mul, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.one_mem, fun τ _ => map_one τ⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.add_mem ha hb, fun τ hτ => by rw [map_add, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.zero_mem, fun τ _ => map_zero τ⟩
  · intro a
    exact ⟨Bt.algebraMap_mem a, fun τ _ => by rw [IsScalarTower.algebraMap_apply O k E]; exact τ.commutes _⟩

theorem exists_comap_valuationSubring {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) :
    ∃ W : ValuationSubring K, W = V.comap (e : K →+* L) ∧ ∀ f : K, f ∈ W ↔ e f ∈ V :=
  ⟨_, rfl, fun f => Iff.rfl⟩

theorem exists_algebra_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) :
    ∃ alg : Algebra R S, ∀ a : R, @algebraMap R S _ _ alg a = ψ a :=
  ⟨ψ.toAlgebra, fun a => rfl⟩

theorem coe_comapEquiv_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) (y : V) :
    (((comapEquiv e V).symm y : V.comap (e : K →+* L)) : K) = e.symm y := rfl

section algEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algEquiv_symm_toRingEquiv_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv (algebraMap R B x) = algebraMap R A x := φ.symm.commutes x

theorem algEquiv_symm_toRingEquiv_symm_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv.symm (algebraMap R A x) = algebraMap R B x := φ.commutes x

theorem algEquiv_symm_toRingEquiv_apply_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv (φ x) = x := φ.symm_apply_apply x

theorem algEquiv_symm_toRingEquiv_symm_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv.symm x = φ x := rfl

end algEquiv

theorem exists_mem_and_maximalIdeal_eq_span {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (V : ValuationSubring L) (W : ValuationSubring K) (hW : W = V.comap (e : K →+* L))
    (π : L) (hπV : π ∈ V) (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(⟨π, hπV⟩ : V)})
    (π' : K) (hπ' : e π' = π) :
    ∃ h : π' ∈ W, IsLocalRing.maximalIdeal W = Ideal.span {(⟨π', h⟩ : W)} := by
  subst hW
  have h : π' ∈ V.comap (e : K →+* L) := by show e π' ∈ V; rw [hπ']; exact hπV
  refine ⟨h, ?_⟩
  rw [maximalIdeal_comap_eq_span e V ⟨π, hπV⟩ hmax]
  congr 2
  apply Subtype.ext
  show e.symm π = π'
  rw [← hπ', e.symm_apply_apply]

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit"

namespace C3Kit2

open IsLocalRing

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

theorem mem_fixedSubfield_of_mem (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : E) (hx : x ∈ K₀) : x ∈ FixedPoints.subfield ↥G E := by
  rw [hK₀, IntermediateField.mem_fixedField_iff] at hx
  show x ∈ MulAction.fixedPoints ↥G E
  rw [MulAction.mem_fixedPoints]
  intro g
  exact hx g g.2

theorem mem_of_mem_fixedSubfield (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : E) (hx : x ∈ FixedPoints.subfield ↥G E) : x ∈ K₀ := by
  rw [hK₀, IntermediateField.mem_fixedField_iff]
  change x ∈ MulAction.fixedPoints ↥G E at hx
  rw [MulAction.mem_fixedPoints] at hx
  intro g hg
  exact hx ⟨g, hg⟩

def fixedEquiv (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (hK₀ : K₀ = IntermediateField.fixedField G) :
    ↥K₀ ≃+* ↥(FixedPoints.subfield ↥G E) where
  toFun x := ⟨(x : E), mem_fixedSubfield_of_mem G K₀ hK₀ x x.2⟩
  invFun y := ⟨(y : E), mem_of_mem_fixedSubfield G K₀ hK₀ y y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

@[scoped simp] theorem coe_fixedEquiv (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : ↥K₀) : ((fixedEquiv G K₀ hK₀ x : ↥(FixedPoints.subfield ↥G E)) : E) = (x : E) := rfl

theorem descDVR {K : Type} [Field K] {k : Type} [Field k] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) [Finite ↥G]
    (W : ValuationSubring K) [IsDiscreteValuationRing ↥W]
    (π : K) (hπG : ∀ g : ↥G, g • π = π) (hπW : π ∈ W)
    (hπ : maximalIdeal ↥W = Ideal.span {(⟨π, hπW⟩ : ↥W)})
    (hfaith : ∀ (g : ↥G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W), g ≠ 1 → ∃ x : ↥W,
      (⟨g • (x : K), (hg x).mpr x.2⟩ - x : ↥W) ∉ maximalIdeal ↥W)
    (B : Subring K) (hBG : ∀ (g : ↥G) (b : K), b ∈ B → g • b ∈ B) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (W₀ : ValuationSubring ↥K₀) (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : K)) ∈ W)
    (hπK₀ : π ∈ K₀) :
    IsDiscreteValuationRing ↥W₀ ∧
    (∃ hπ0 : (⟨π, hπK₀⟩ : ↥K₀) ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπ0⟩ : ↥W₀)}) ∧
    (∀ f : K, (∀ g : ↥G, g • f = f) →
      (f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
        (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)) := by
  obtain ⟨h1, ⟨hπ0, h2⟩, h3⟩ :=
    ValuationSubring.maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
      K (↥G) W π hπG hπW hπ hfaith B hBG hBW hloc
  haveI := h1
  let e := fixedEquiv G K₀ hK₀
  have hWeq : W₀ = (W.comap (FixedPoints.subfield ↥G K).subtype).comap (e : ↥K₀ →+* ↥(FixedPoints.subfield ↥G K)) := by
    ext f; rw [hW₀]; rfl
  refine ⟨?_, ?_, h3⟩
  · rw [hWeq]; exact S3GlueKit.isDiscreteValuationRing_comap e _
  · have hmem : (⟨π, hπK₀⟩ : ↥K₀) ∈ W₀ := (hW₀ _).mpr hπW
    refine ⟨hmem, ?_⟩

    have key := S3GlueKit.maximalIdeal_comap_eq_span e (W.comap (FixedPoints.subfield ↥G K).subtype) ⟨_, hπ0⟩ h2
    have hgen : ((S3GlueKit.comapEquiv e (W.comap (FixedPoints.subfield ↥G K).subtype)).symm ⟨_, hπ0⟩ :
        ↥((W.comap (FixedPoints.subfield ↥G K).subtype).comap (e : ↥K₀ →+* ↥(FixedPoints.subfield ↥G K)))) =
        ⟨⟨π, hπK₀⟩, by rw [← hWeq]; exact hmem⟩ := by
      apply Subtype.ext; apply Subtype.ext; rfl
    rw [hgen] at key
    subst hWeq
    exact key

theorem hloc_reshape {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K]
    (Bt : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (hR3e : ∀ f : K, f ∈ W ↔ ∃ g h : ↥Bt, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K)) :
    ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g := by
  intro f
  rw [hR3e]
  constructor
  · rintro ⟨g, h, hh, hf⟩
    exact ⟨g, h, g.2, h.2, fun _ => hh, hf⟩
  · rintro ⟨g, h, hg, hh, hu, hf⟩
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, hu _, hf⟩

end C3Kit2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

namespace C3Kit3

open MvPolynomial DrinfeldCurve

theorem x_ne_zero (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] : DrinfeldCurve.x q k ≠ 0 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hP1 : (Polynomial.X ^ q - Polynomial.X : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] ; omega
  have hP : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> rw [hP1]
    rw [Polynomial.natDegree_one]; omega
  have hP0 : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hP; omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k)
    (by rw [Polynomial.degree_eq_natDegree hP0, hP]; exact_mod_cast (show q ≠ 0 by omega))
  have ha' : a ^ q - a + 1 = 0 := by
    have := ha.eq_zero
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] using this
  have ha0 : a ≠ 0 := by rintro rfl; simp [zero_pow (show q ≠ 0 by omega)] at ha'

  let φ : MvPolynomial (Fin 2) k →ₐ[k] k := MvPolynomial.aeval ![a, 1]
  have hφ : ∀ f ∈ drinfeldIdeal q k, φ f = 0 := by
    intro f hf
    rw [drinfeldIdeal, Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    rw [map_mul]
    have : φ (drinfeldPoly q k - 1) = 0 := by
      simp only [drinfeldPoly, φ, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow, mul_one]
      linear_combination (-1 : k) * ha'
    rw [this, zero_mul]
  let ψ : CoordRing q k →ₐ[k] k := Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ
  have hψx : ψ (DrinfeldCurve.x q k) = a := by
    show Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ (Ideal.Quotient.mkₐ k (drinfeldIdeal q k) (X 0)) = a
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp [φ]
  intro hx
  apply ha0
  rw [← hψx, hx, map_zero]

theorem hAction_x_ne (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [Algebra (GaloisField q 2) k]
    (p : ↥(hSubgroup q))
    (hp1 : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1)
    (hp2 : scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1) :
    hAction q k p (DrinfeldCurve.x q k) ≠ DrinfeldCurve.x q k := by
  set s := scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 with hs
  have hact : hAction q k p (DrinfeldCurve.x q k) = s • DrinfeldCurve.x q k := by
    show hAction q k p (mk q k (X 0)) = s • mk q k (X 0)
    rw [hAction_mk, hp1]
    have : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := rfl
    rw [this, substPoly_one, AlgHom.id_apply, scalePoly_X, map_mul, ← hs]
    rw [show mk q k (C s) = algebraMap k (CoordRing q k) s from (mk q k).commutes s, Algebra.smul_def]
  intro h
  rw [hact] at h
  have h2 : (s - 1) • DrinfeldCurve.x q k = 0 := by rw [sub_smul, one_smul, h, sub_self]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hp2
  exact x_ne_zero q k ((inv_smul_smul₀ hs1 (DrinfeldCurve.x q k)).symm.trans (by rw [h2, smul_zero]))

end C3Kit3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

namespace C3Kit

section Action

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {R : Type*} [CommRing R] [Algebra R K]

def subalgAction (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul τ b := ⟨(τ : K ≃ₐ[k] K) (b : K), h τ τ.2 b b.2⟩
  one_smul b := Subtype.ext rfl
  mul_smul σ τ b := Subtype.ext rfl
  smul_zero τ := Subtype.ext (map_zero _)
  smul_add τ a b := Subtype.ext (map_add _ _ _)
  smul_one τ := Subtype.ext (map_one _)
  smul_mul τ a b := Subtype.ext (map_mul _ _ _)

theorem subalgAction_smul_coe (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) (τ : ↥G) (b : ↥B) :
    letI := subalgAction G B h
    (((τ • b) : ↥B) : K) = (τ : K ≃ₐ[k] K) (b : K) := rfl

def inclAlgebra (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) : Algebra ↥B₀ ↥B :=
  (Subalgebra.inclusion hle).toRingHom.toAlgebra

theorem inclAlgebra_algebraMap_coe (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) (x : ↥B₀) :
    letI := inclAlgebra B₀ B hle
    ((algebraMap ↥B₀ ↥B x : ↥B) : K) = (x : K) := rfl

theorem inclAlgebra_isScalarTower (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    IsScalarTower R ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)

theorem inclAlgebra_faithfulSMul (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    FaithfulSMul ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  (faithfulSMul_iff_algebraMap_injective ↥B₀ ↥B).mpr (Subalgebra.inclusion_injective hle)

theorem isGaloisGroup (G : Subgroup (K ≃ₐ[k] K)) (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K)) :
    letI := subalgAction G B h
    letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
    IsGaloisGroup ↥G ↥B₀ ↥B := by
  letI := subalgAction G B h
  letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
  refine ⟨⟨fun {σ τ} hστ => ?_⟩, ⟨fun τ b₀ b => ?_⟩, ⟨fun b hb => ?_⟩⟩
  ·
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    obtain ⟨g, h', hh0, hfg⟩ := hfrac f
    have eg : (σ : K ≃ₐ[k] K) (g : K) = (τ : K ≃ₐ[k] K) (g : K) := congrArg Subtype.val (hστ g)
    have eh : (σ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (h' : K) := congrArg Subtype.val (hστ h')
    have hσh : (σ : K ≃ₐ[k] K) (h' : K) ≠ 0 := (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
    have e1 : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) (h' : K) = (σ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    have e2 : (τ : K ≃ₐ[k] K) f * (τ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    rw [← mul_left_inj' hσh, e1, eg, eh, ← e2]
  ·
    apply Subtype.ext
    change (τ : K ≃ₐ[k] K) ((b₀ : K) * (b : K)) = (b₀ : K) * (τ : K ≃ₐ[k] K) (b : K)
    rw [map_mul, ((hB₀ b₀).mp b₀.2).2 τ τ.2]
  ·
    refine ⟨⟨(b : K), (hB₀ b).mpr ⟨b.2, fun τ hτ => ?_⟩⟩, Subtype.ext rfl⟩
    exact congrArg Subtype.val (hb ⟨τ, hτ⟩)

theorem smulCommClass (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    [Algebra R k] [IsScalarTower R k K] :
    letI := subalgAction G B h
    SMulCommClass ↥G R ↥B := by
  letI := subalgAction G B h
  refine ⟨fun τ r b => Subtype.ext ?_⟩
  change (τ : K ≃ₐ[k] K) ((r • b : ↥B) : K) = ((r • (τ • b) : ↥B) : K)
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply R k K, AlgEquiv.commutes]
  rfl

end Action
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

end C3Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

namespace C3Kit4

theorem exists_invariant_fraction {k K : Type*} [Field k] [Field K] [Algebra k K] {R : Type*} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) [Finite ↥G] (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K))
    (f : K) (hf : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f) :
    ∃ g h' : ↥B₀, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K) := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite _
  obtain ⟨g, h', hh0, hfg⟩ := hfrac f

  let N : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (h' : K)
  have hNB : N ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hN0 : N ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
  have hNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ N = N := by
    intro τ hτ
    simp only [N, map_prod]
    simp_rw [← AlgEquiv.mul_apply]
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨τ, hτ⟩) _ _ (fun σ => rfl)

  let P : K := ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, (σ : K ≃ₐ[k] K) (h' : K)
  have hPB : P ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hNP : N = (h' : K) * P := by
    simp only [N, P]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ↥G) _ (Finset.mem_univ (1 : ↥G))]
    rfl
  have hfN : f * N = (g : K) * P := by rw [hNP, ← mul_assoc, hfg]
  have hfNB : f * N ∈ B := by rw [hfN]; exact B.mul_mem g.2 hPB
  have hfNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (f * N) = f * N := by
    intro τ hτ; rw [map_mul, hf τ hτ, hNinv τ hτ]
  exact ⟨⟨f * N, (hB₀ _).mpr ⟨hfNB, hfNinv⟩⟩, ⟨N, (hB₀ _).mpr ⟨hNB, hNinv⟩⟩, hN0, rfl⟩

end C3Kit4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

namespace C3GlueKit
open IsLocalRing

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]

theorem prime_and_loc_of_invariants
    (G : Subgroup (K ≃ₐ[k] K)) (Bt B₀ : Subalgebra O K) (Wt : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ Bt → f ∈ Wt)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (π : O) (hπm : (⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt) ∈ maximalIdeal ↥Wt)
    (hπne : algebraMap O K π ≠ 0)
    (hGO : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (algebraMap O K π) = algebraMap O K π)
    (P : (K ≃ₐ[k] K) → Prop) (hPG : ∀ τ, P τ → τ ∈ G)
    (hR5c : ∀ b : ↥Bt, (∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ (b : K) ∈ Bt,
        (⟨τ (b : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) → algebraMap O ↥Bt π ∣ b)
    (K₀ : IntermediateField k K) (hK₀B₀ : ∀ f : K, f ∈ B₀ → f ∈ K₀)
    (hK₀G : ∀ f : K, f ∈ K₀ → ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (W₀ : ValuationSubring ↥K₀) (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : K)) ∈ Wt)
    (hloc : ∀ f : K, (∀ g : ↥G, g • f = f) →
      (f ∈ Wt ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
        (∀ hh : h ∈ Wt, (⟨h, hh⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧ f * h = g)) :
    (∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b)) ∧
    Prime (algebraMap O ↥B₀ π) ∧
    (∀ f : ↥K₀, f ∈ W₀ ↔ ∃ g h : ↥B₀, ¬ (algebraMap O ↥B₀ π ∣ h) ∧ (f : K) * (h : K) = (g : K)) := by
  have hcoeπ : ((algebraMap O ↥B₀ π : ↥B₀) : K) = algebraMap O K π := Subalgebra.coe_algebraMap B₀ π
  have KEY : ∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b) := by
    intro b
    obtain ⟨hbBt, hbfix⟩ := (hB₀ _).mp b.2
    constructor
    · intro hm
      have hprem : ∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K) ∈ Bt,
          (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := by
        intro τ hP hb
        have e : τ (b : K) = (b : K) := hbfix τ (hPG τ hP)
        have : (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) = ⟨(b : K), hBW _ hbBt⟩ := Subtype.ext e
        rw [this]; exact hm
      obtain ⟨c, hc⟩ := hR5c ⟨(b : K), hbBt⟩ hprem
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥Bt => (z : K)) hc
        simpa [Subalgebra.coe_algebraMap] using this
      have hcfix : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (c : K) = (c : K) := by
        intro τ hτ
        have h1 := hbfix τ hτ
        rw [hcK, map_mul, hGO τ hτ] at h1
        exact mul_left_cancel₀ hπne h1
      have hcB₀ : (c : K) ∈ B₀ := (hB₀ _).mpr ⟨c.2, hcfix⟩
      refine ⟨⟨(c : K), hcB₀⟩, Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hcoeπ]; exact hcK
    · rintro ⟨c, hc⟩
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥B₀ => (z : K)) hc
        beta_reduce at this
        rw [Subalgebra.coe_mul, hcoeπ] at this; exact this
      have hcW : (c : K) ∈ Wt := hBW _ ((hB₀ _).mp c.2).1
      have : (⟨(b : K), hBW _ hbBt⟩ : ↥Wt) = ⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ * ⟨(c : K), hcW⟩ :=
        Subtype.ext hcK
      rw [this]
      exact Ideal.mul_mem_right _ _ hπm
  refine ⟨KEY, ?_, ?_⟩
  ·
    have hmprime : (maximalIdeal ↥Wt).IsPrime := Ideal.IsMaximal.isPrime inferInstance
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      apply hπne
      have := congrArg (fun z : ↥B₀ => (z : K)) h0
      beta_reduce at this
      rw [hcoeπ] at this; simpa using this
    · intro hu
      have hu' : IsUnit ((⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt)) := by
        obtain ⟨u, hu⟩ := hu
        have hval : ((u : ↥B₀) : K) = algebraMap O K π := by rw [hu, hcoeπ]
        have hinv : ((u⁻¹ : (↥B₀)ˣ) : ↥B₀) * (u : ↥B₀) = 1 := u.inv_mul
        refine isUnit_iff_exists_inv'.mpr ⟨⟨((u⁻¹ : (↥B₀)ˣ) : ↥B₀), hBW _ ((hB₀ _).mp ((u⁻¹ : (↥B₀)ˣ) : ↥B₀).2).1⟩, Subtype.ext ?_⟩
        have := congrArg (fun z : ↥B₀ => (z : K)) hinv
        beta_reduce at this
        rw [Subalgebra.coe_mul, hval, Subalgebra.coe_one] at this
        exact this
      exact (mem_maximalIdeal _ |>.mp hπm) hu'
    · intro a b hab
      rw [← KEY] at hab ⊢; rw [← KEY]
      have : (⟨((a * b : ↥B₀) : K), hBW _ ((hB₀ _).mp (a * b).2).1⟩ : ↥Wt) =
          ⟨(a : K), hBW _ ((hB₀ _).mp a.2).1⟩ * ⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ := Subtype.ext (Subalgebra.coe_mul B₀ a b)
      rw [this] at hab
      exact hmprime.mem_or_mem hab
  ·
    intro f
    rw [hW₀, hloc (f : K) (fun g => hK₀G _ f.2 g g.2)]
    constructor
    · rintro ⟨g, h, hg, hh, hgfix, hhfix, hunit, hfh⟩
      have hgB₀ : g ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hg, fun τ hτ => hgfix ⟨τ, hτ⟩⟩
      have hhB₀ : h ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hh, fun τ hτ => hhfix ⟨τ, hτ⟩⟩
      refine ⟨⟨g, hgB₀⟩, ⟨h, hhB₀⟩, fun hd => ?_, hfh⟩
      have hm := (KEY ⟨h, hhB₀⟩).mpr hd
      exact hunit _ hm
    · rintro ⟨g, h, hnd, hfh⟩
      refine ⟨(g : K), (h : K), Subalgebra.mem_toSubring.mpr ((hB₀ _).mp g.2).1, Subalgebra.mem_toSubring.mpr ((hB₀ _).mp h.2).1, fun σ => ((hB₀ _).mp g.2).2 σ σ.2,
        fun σ => ((hB₀ _).mp h.2).2 σ σ.2, fun hh hm => hnd ((KEY h).mp ?_), hfh⟩
      have : (⟨(h : K), hh⟩ : ↥Wt) = ⟨(h : K), hBW _ ((hB₀ _).mp h.2).1⟩ := rfl
      rw [← this]; exact hm

end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

namespace C3GlueKit
section kitW
open IsLocalRing

theorem mem_iff_map_mem_of_pow_eq_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    {S : Type*} [SetLike S K] (B : S) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)
    (μ : K ≃ₐ[k] K) (n : ℕ) (hn : 0 < n) (hμn : μ ^ n = 1)
    (hμB : ∀ f : K, f ∈ B → μ f ∈ B)
    (hμP : ∀ (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨μ f, hBW _ (hμB f hf)⟩ : ↥W) ∈ maximalIdeal ↥W)
    (f : K) : f ∈ W ↔ μ f ∈ W := by

  have hμmB : ∀ (m : ℕ) (f : K), f ∈ B → (μ ^ m) f ∈ B := by
    intro m; induction m with
    | zero => intro f hf; simpa using hf
    | succ m ih => intro f hf; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (hμB f hf)
  have hμmP : ∀ (m : ℕ) (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W →
      (⟨(μ ^ m) f, hBW _ (hμmB m f hf)⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro m; induction m with
    | zero => intro f hf h; simpa using h
    | succ m ih =>
      intro f hf h
      have h1 := ih _ (hμB f hf) (hμP f hf h)
      have e : (μ ^ (m + 1)) f = (μ ^ m) (μ f) := by rw [pow_succ, AlgEquiv.mul_apply]
      have : (⟨(μ ^ (m + 1)) f, hBW _ (hμmB (m + 1) f hf)⟩ : ↥W) = ⟨(μ ^ m) (μ f), hBW _ (hμmB m _ (hμB f hf))⟩ := Subtype.ext e
      rw [this]; exact h1

  have hμP' : ∀ (h : K) (hh : h ∈ B), (⟨μ h, hBW _ (hμB h hh)⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨h, hBW h hh⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro h hh hm
    have h1 := hμmP (n - 1) (μ h) (hμB h hh) hm
    have e : (μ ^ (n - 1)) (μ h) = h := by
      rw [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply]
    have : (⟨(μ ^ (n - 1)) (μ h), hBW _ (hμmB (n - 1) _ (hμB h hh))⟩ : ↥W) = ⟨h, hBW h hh⟩ := Subtype.ext e
    rw [← this]; exact h1

  have fwd : ∀ f : K, f ∈ W → μ f ∈ W := by
    intro f hf
    obtain ⟨g, h, hg, hh, hunit, hfh⟩ := (hloc f).mp hf
    refine (hloc (μ f)).mpr ⟨μ g, μ h, hμB g hg, hμB h hh, fun hh' hm => hunit (hBW h hh) (hμP' h hh ?_), by rw [← map_mul, hfh]⟩
    have : (⟨μ h, hh'⟩ : ↥W) = ⟨μ h, hBW _ (hμB h hh)⟩ := rfl
    rw [← this]; exact hm
  refine ⟨fwd f, fun hμf => ?_⟩
  have h1 : (μ ^ (n - 1)) (μ f) ∈ W := by
    have : ∀ (m : ℕ) (x : K), x ∈ W → (μ ^ m) x ∈ W := by
      intro m; induction m with
      | zero => intro x hx; simpa using hx
      | succ m ih => intro x hx; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (fwd x hx)
    exact this _ _ hμf
  rwa [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply] at h1

theorem exists_prime_pullback {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]
    (Bt : Subalgebra O K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (τ : K ≃ₐ[k] K) (hτB : ∀ f : K, f ∈ Bt → τ f ∈ Bt) :
    ∃ Q : Ideal ↥Bt, Q.IsPrime ∧
      ∀ b : ↥Bt, b ∈ Q ↔ (⟨τ (b : K), hBW _ (hτB _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := by
  let φ : ↥Bt →+* ↥W :=
    { toFun := fun b => ⟨τ (b : K), hBW _ (hτB _ b.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨(maximalIdeal ↥W).comap φ, Ideal.comap_isPrime φ (maximalIdeal ↥W), fun b => ?_⟩
  rw [Ideal.mem_comap]; exact Iff.rfl

end kitW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

namespace C3GlueKit
section kitK4
open IsLocalRing

theorem mem_maximalIdeal_of_restrict {k E : Type*} [Field k] [Field E] [Algebra k E]
    (K₀ : IntermediateField k E) (Wt : ValuationSubring E) (W₀ : ValuationSubring ↥K₀)
    (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : E)) ∈ Wt)
    (x : ↥W₀) (hx : (⟨((x : ↥K₀) : E), (hW₀ _).mp x.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) :
    x ∈ maximalIdeal ↥W₀ := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  obtain ⟨u, hu⟩ := hu
  have hinv : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := u.inv_mul
  refine isUnit_iff_exists_inv'.mpr ⟨⟨(((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀), (hW₀ _).mp ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2⟩, Subtype.ext ?_⟩
  have h1 := congrArg (fun z : ↥W₀ => (((z : ↥K₀)) : E)) hinv
  beta_reduce at h1
  show (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((x : ↥K₀) : E) = 1
  rw [← hu]
  have h2 : (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) : ↥W₀) : ↥K₀) : E) =
      (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((((u : ↥W₀)) : ↥K₀) : E) := rfl
  rw [← h2, h1]; rfl

end kitK4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.S3GlueKit P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd.C3Kit2"

set_option maxHeartbeats 0 in

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (hq2 : q = 2)
    (M' : ℕ)
    [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ξ : ↥k₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (hqM' : ¬ q ∣ M')
    (hA : A.LiesOverPrime q)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue ↥A) y)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (hℓ : ℓ.Prime)
    (hℓ3 : 3 ≤ ℓ)
    (hℓq : ℓ ≠ q)
    (hℓM' : ¬ ℓ ∣ M')
    (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    (hKb : Kb = ⊥)
    (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb})
    (hϖb0 : ϖb ≠ 0)
    (htame : IsUnit (((ℓg - 1) / 2 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hξ : IsPrimitiveRoot ξ q)
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hϖt' : (ϖt' : ↥k₀) = ϖt)
    (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)
    (hover : (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
          (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hOrbit : ∀ y' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y'.IsMaximal →
        algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y' →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
              (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
                  algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y') →
        ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
          (∀ f : ↥Kℓ, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
            τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∧
          (∀ (f : ↥Kℓ) (hf : f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
            (hf' : τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            (⟨f, hf⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y ↔ (⟨τ f, hf'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'))
    (hS1 :
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ≤ Bt ∧
        (∀ f : ↥Kℓ, ∃ g h : ↥Bt, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧
        Ring.KrullDimLE 1 (↥Bt ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩}) ∧

        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wt ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
        maximalIdeal ↥Wt = Ideal.span {(⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ : ↥Wt)} ∧
        IsDiscreteValuationRing ↥Wt ∧
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔
          ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
        (∀ f : ↥Kℓ, f ∈ Wt ↔ ∃ g h : ↥Bt, (⟨(h : ↥Kℓ), hBW _ h.2⟩ : ↥Wt) ∉ maximalIdeal ↥Wt ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
          ∃ (ρ : ↥Bt →+* DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
            Function.Surjective ρ ∧
            (∀ b : ↥Bt, ρ b = 0 ↔ (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt a) = algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)) ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) →
                ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                  (∀ (b : ↥Bt) (hb : τ (b : ↥Kℓ) ∈ Bt), ρ ⟨τ (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem⟩ (ρ b)) ∧
                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥Kℓ, τ k = k) → c ≠ 1) ∧

                  (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
                      (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ') (_ : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ' f ∈ Wt)
                      (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ (b : ↥Bt) (hb : τ' (b : ↥Kℓ) ∈ Bt), ρ ⟨τ' (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem'⟩ (ρ b)))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt) ∧
        (∀ Q : Ideal ↥Bt, Q.IsPrime → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q →
          ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
            ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
              ∀ b : ↥Bt, (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt → τ (b : ↥Kℓ) ∈ Bt ∧ ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hb⟩ : ↥Bt) ∈ Q) ∧
        (∀ b : ↥Bt, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
          algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b))
    (hn1 : 1 ≤ n)
    (hnq : n ∣ q + 1)
    (hγ₀Γ : γ₀ ∈ CongruenceSubgroup.Gamma q)
    (hγ₀Γ0 : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ₀⁻¹ Kℓ τ₀)
    (hτ₀W : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ₀ f ∈ Wt)
    (hm1 : 1 ≤ m)
    (hm : ∃ w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit w ∧ ⟨π₀, hπ⟩ ^ m = ϖt' * w)
    (hζc : ζc ^ n = 1)
    (hζcprim : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζc ^ k - 1))
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (hR7 : (∀ f : ↥Kℓ, f ∈ Bt → (τ₀ ^ n) f = f) ∧
          (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥Kℓ, f ∈ Bt ∧ (τ₀ ^ k) f ≠ f) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∃ k : ℕ, k < n ∧ ∀ f : ↥Kℓ, f ∈ Bt → τ f = (τ₀ ^ k) f) ∧
          ends.card = q + 1 ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧ ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ₀ f ∈ O) ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : ↥Kℓ) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∃ Bc : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ, Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bc ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ∀ f : ↥Kℓ, f ∈ Bc → τ f ∈ Bc) ∧
            ∀ O ∈ ends, (∀ f : ↥Kℓ, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ O ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ O → τ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧
          (∀ O ∈ ends,

            (∀ f : ↥Kℓ, f ∈ O → f ∈ Wt) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ O) ∧
            (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ O ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
            (∀ (f : ↥Kℓ) (hf : f ∈ O), ∃ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

            (∃ (hϖO : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))] (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (ζc' : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ζc * ζc' = 1)
               (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))),
              cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
              (∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) a)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              (∀ hcy : (cy : ↥Kℓ) ∈ Wt, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
              (∀ hcx : (cx : ↥Kℓ) ∈ Wt, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧

              (∃ (hjaO : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaO⟩) =
                  (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ^ e) ∧
              (∀ (f : ↥Kℓ) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
              θ₀ (UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧
              θ₀ (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc' * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧

              (∃ Wx : ValuationSubring ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ O → f ∈ Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) ∧
                (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hϖWx : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}) ∧
                (∃ (t : ↥Wx), ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (t : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧

                (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
                (∀ hcx : (cx : ↥Kℓ) ∈ Wx, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥Kℓ) ∈ Wx, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) ∧
                (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧

                (∀ O' ∈ ends, O' ≠ O → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) ∧

                (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = O)) ∧

              (∃ Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Bt ∧ f ∈ O) ∧
                Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx ∧
                (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    ∀ f : ↥Kℓ, f ∈ Bx → τ f ∈ Bx) ∧
                (∀ f : ↥Kℓ, f ∈ Bx → ∀ P : AlgebraicCurve.Place ↥k₀ ↥Kℓ, 0 ≤ P.ord jℓ → 0 ≤ P.ord f) ∧
                (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧

                (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ O ∧ f ∉ V) → b ∉ V))))) ∧

          (∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y → ∀ hb : (b : ↥Kℓ) ∈ V, (⟨(b : ↥Kℓ), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ Bt → f ∈ V) ∨
            (∃ O ∈ ends, ∀ (f : ↥Kℓ) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))))
    (hR9 : (∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                  (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) → b ∉ V)))
    (hR10 : (∀ y'' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y''.IsMaximal → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y'' →
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ¬ (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'')) →
            ∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ V : ValuationSubring ↥Kℓ,
                (∀ c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (c : ↥Kℓ) ∈ V) →
                (∀ (c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hc : τ.symm (c : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    (⟨τ.symm (c : ↥Kℓ), hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'' → ∀ hcV : (c : ↥Kℓ) ∈ V, (⟨(c : ↥Kℓ), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                b ∉ V))
    (hn : n = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)
    :
        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ := by
  haveI hℓgFact : Fact ℓg.Prime := ⟨hℓg⟩
  classical

  obtain ⟨ι, hι'⟩ := C3aux_exists_emb k₀ q ξ hξ
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩
  obtain ⟨huniq, hmul, hone⟩ := ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
      q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
      q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ H₁ hH₁ Kℓ hKℓ

  have hGle : G ≤ Gfull := by
    rw [hG, Subgroup.closure_le]
    rintro τ ⟨γ, -, hγ0, hτ⟩
    exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
  haveI hGfinite : Finite ↥G := by
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ := by
    intro τ hτ
    rw [hG] at hτ
    refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
        γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) ?_ ?_ ?_ ?_ hτ
    · intro τ h; exact h
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [inv_one]; exact hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)⟩
    · rintro τ σ - - ⟨γ, hγq, hγ0, hτ⟩ ⟨δ, hδq, hδ0, hσ⟩
      refine ⟨γ * δ, Subgroup.mul_mem _ hγq hδq, Subgroup.mul_mem _ hγ0 hδ0, ?_⟩
      rw [mul_inv_rev]
      exact hmul γ⁻¹ δ⁻¹ (Subgroup.inv_mem _ hγ0) (Subgroup.inv_mem _ hδ0) τ σ hτ hσ
    · rintro τ - ⟨γ, hγq, hγ0, hτ⟩
      obtain ⟨σ, hσ⟩ := hex γ⁻¹ (Subgroup.inv_mem _ hγ0)
      rw [inv_inv] at hσ

      have h1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ (γ * γ⁻¹) Kℓ (τ * σ) := hmul γ⁻¹ γ (Subgroup.inv_mem _ hγ0) hγ0 τ σ hτ hσ
      rw [mul_inv_cancel] at h1
      have h2 : τ * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1 (hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp))
      have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
      refine ⟨γ⁻¹, Subgroup.inv_mem _ hγq, Subgroup.inv_mem _ hγ0, ?_⟩
      rw [inv_inv, h3]; exact hσ

  obtain ⟨hR1a, hR1b, hR2a, hR2b, hR2c, hR3a, hR3b, hR3c, hR3d, hR3e, hR46, hR5a, hR5b, hR5c⟩ := id hS1
  have hGBt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt := by
    intro τ hτ f hf
    obtain ⟨γ, -, hγ0, hτ'⟩ := hGatt τ hτ
    exact hR5a γ hγ0 τ hτ' f hf

  have hB₀le : B₀ ≤ Bt := fun f hf => ((hB₀ f).mp hf).1
  letI instAct : MulSemiringAction ↥G ↥Bt := C3Kit.subalgAction G Bt hGBt
  letI instAlg : Algebra ↥B₀ ↥Bt := C3Kit.inclAlgebra B₀ Bt hB₀le
  haveI instIST : IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt := C3Kit.inclAlgebra_isScalarTower B₀ Bt hB₀le
  haveI instFS : FaithfulSMul ↥B₀ ↥Bt := C3Kit.inclAlgebra_faithfulSMul B₀ Bt hB₀le
  haveI instGal : IsGaloisGroup ↥G ↥B₀ ↥Bt := C3Kit.isGaloisGroup G Bt B₀ hGBt hB₀ hR1b
  haveI instSCC : SMulCommClass ↥G ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := C3Kit.smulCommClass G Bt hGBt
  haveI : Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := hR2b
  haveI hdvr0 : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr

  have hGunit : IsUnit ((Nat.card ↥G : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    obtain ⟨-, hGdvd⟩ := ModularCurve.FullLevel.AuxLevelOne.finite_and_natCard_dvd_div_two_of_eq_closure_isLevelAutAt_gamma_of_eq_two_of_dvd q hq2 M' hqM' ℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ G hG
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hGdvd) htame

  have hC1 := IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt ↥G hGunit
  obtain ⟨hB₀ft, hB₀fp, hBtfin, hB₀normal, hB₀flat, hB₀fib, hB₀smooth⟩ := hC1

  have hπW : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wt := hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)
  have hπeq : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = algebraMap ↥k₀ ↥Kℓ π₀ :=
    IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ ⟨π₀, hπ⟩
  have hπG : ∀ g : ↥G, g • algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ := by
    intro g
    rw [hπeq]
    exact (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).commutes π₀
  have hπK₀ : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ K₀ := by
    rw [hπeq]; exact K₀.algebraMap_mem π₀
  have hBG' : ∀ (g : ↥G) (b : ↥Kℓ), b ∈ Bt.toSubring → g • b ∈ Bt.toSubring := fun g b hb => hGBt g g.2 b hb
  have hloc' := C3Kit2.hloc_reshape Bt Wt hBW hR3e
  haveI hWtdvr : IsDiscreteValuationRing ↥Wt := hR3c

  have hqp : q.Prime := Fact.out
  have hqmem : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hqA : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      have hq' : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
      rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqA
    apply hqA
    obtain ⟨v, hv⟩ := hu
    refine isUnit_iff_exists_inv.mpr ⟨⟨(((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀), ((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2⟩, Subtype.ext ?_⟩
    have e := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => (((z : ↥k₀)) : AlgebraicClosure ℚ)) v.mul_inv
    rw [hv] at e
    push_cast at e ⊢
    simpa using e
  haveI hchar : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q := by
    have h0 : ((q : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsLocalRing.residue_eq_zero_iff]; exact hqmem
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0
  haveI hresI : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hres
  letI instZ : Algebra (ZMod q) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := ZMod.algebra (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q
  letI instGF : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    (IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).toRingHom.toAlgebra

  have hfaith : ∀ (g : ↥G) (hg : ∀ x : ↥Kℓ, g • x ∈ Wt ↔ x ∈ Wt), g ≠ 1 → ∃ x : ↥Wt,
      (⟨g • (x : ↥Kℓ), (hg x).mpr x.2⟩ - x : ↥Wt) ∉ maximalIdeal ↥Wt := by
    intro g hg hne
    obtain ⟨γ, hγq, hγ0, hτ⟩ := hGatt g g.2
    obtain ⟨ρ, hρsurj, hρker, -, hρeq⟩ := hR46 instGF
    have hdec : ∀ f : ↥Kℓ, f ∈ Wt ↔ (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) f ∈ Wt := fun f => (hg f).symm
    obtain ⟨c, hmem, hcomm, hc, -⟩ := hρeq γ hγ0 (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) hτ hdec
    have hne' : ¬ ∀ x : ↥Kℓ, (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) x = x := by
      intro hall; apply hne
      apply Subtype.ext; apply AlgEquiv.ext; intro x
      rw [hall x]; rfl
    have hc1 : c ≠ 1 := hc hγq hne'

    have hp1 : ((⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ : ↥(DrinfeldCurve.hSubgroup q)) :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1 := by
      show ModularCurve.FullLevel.redQ q γ = 1
      show Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))) γ) = 1
      rw [CongruenceSubgroup.Gamma_mem'.mp hγq, map_one]
    have hp2 : DrinfeldCurve.scalarOf q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
        ((⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ : ↥(DrinfeldCurve.hSubgroup q)) :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1 := by
      show algebraMap (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (c : GaloisField q 2) ≠ 1
      intro h1
      apply hc1
      apply Units.ext
      exact (algebraMap (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))).injective (h1.trans (map_one _).symm)
    have hmove := C3Kit3.hAction_x_ne q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ hp1 hp2

    obtain ⟨b, hb⟩ := hρsurj (DrinfeldCurve.x q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    have hbτ : (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (b : ↥Kℓ) ∈ Bt := hGBt g g.2 b b.2
    refine ⟨⟨(b : ↥Kℓ), hBW _ b.2⟩, ?_⟩
    intro hmax
    apply hmove

    have hdiff : (ρ (⟨(g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (b : ↥Kℓ), hbτ⟩ - b) = 0) := by
      rw [hρker]
      exact hmax
    rw [map_sub, hcomm b hbτ, hb, sub_eq_zero] at hdiff
    exact hdiff
  obtain ⟨hW₀dvr, ⟨hπ0, hW₀max⟩, hW₀loc⟩ := C3Kit2.descDVR G Wt (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩) hπG hπW hR3b hfaith
    Bt.toSubring hBG' hBW hloc' K₀ hK₀ W₀' hW₀' hπK₀

  have hπelt : algebraMap ↥k₀ ↥K₀ π₀ = (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hπK₀⟩ : ↥K₀) := Subtype.ext hπeq.symm
  have hB₀K₀ : ∀ f : ↥Kℓ, f ∈ B₀ → f ∈ K₀ := by
    intro f hf
    rw [hK₀, IntermediateField.mem_fixedField_iff]
    exact ((hB₀ f).mp hf).2

  have hπne : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (R := ↥Wt)
    rw [hR3b, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h0
  have hGO : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ :=
    fun τ _ => by rw [hπeq]; exact τ.commutes π₀
  have hPG : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) → τ ∈ G :=
    fun τ h => by rw [hG]; exact Subgroup.subset_closure h
  have hR5c' : ∀ b : ↥Bt, (∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) →
      ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b :=
    fun b h => hR5c b (fun γ hγq hγ0 τ hτ hb => h τ ⟨γ, hγq, hγ0, hτ⟩ hb)
  have hK₀G : ∀ f : ↥Kℓ, f ∈ K₀ → ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f := by
    intro f hf; rw [hK₀, IntermediateField.mem_fixedField_iff] at hf; exact hf
  have hKEY := C3GlueKit.prime_and_loc_of_invariants G Bt B₀ Wt hBW hB₀ ⟨π₀, hπ⟩
    (by rw [hR3b]; exact Ideal.mem_span_singleton_self _) hπne hGO _ hPG hR5c' K₀ hB₀K₀ hK₀G W₀' hW₀' hW₀loc
  obtain ⟨KEY, hM2b, hM2c⟩ := hKEY

  haveI : Module.IsTorsionFree ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun c x h => ?_)
    have h1 : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ c * (x : ↥Kℓ) = 0 := by
      have e := congrArg (fun z : ↥Bt => (z : ↥Kℓ)) h
      simp only [Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_zero] at e
      exact e
    rcases mul_eq_zero.mp h1 with h2 | h2
    · left
      rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ, map_eq_zero] at h2
      exact IsFractionRing.injective ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ (by rw [h2, map_zero])
    · right; exact Subtype.ext h2
  haveI hflat : Module.Flat ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := inferInstance

  have hjqK : (coeffEmb ↥k₀ jq : LaurentSeries ↥k₀) ∈ Kℓ := by rw [← hjℓ]; exact jℓ.2
  have hjB₀ : (⟨_, hjqK⟩ : ↥Kℓ) ∈ B₀ := by
    have hjℓeq : jℓ = ⟨coeffEmb ↥k₀ jq, hjqK⟩ := Subtype.ext hjℓ
    have hjBt : (⟨_, hjqK⟩ : ↥Kℓ) ∈ Bt := by
      apply hR1a
      rw [← hjℓeq]; exact (AlgebraicCurve.TwoChartIntegralModel.jChartFin _ _ jℓ).2
    refine (hB₀ _).mpr ⟨hjBt, fun τ hτ => ?_⟩
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hGatt τ hτ
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    have hx0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' 1 (q ^ 2 * M')
      ⟨q ^ 2, by ring⟩ (ModularCurve.FullLevel.levelH q M') jq (modularFunctionField_le_full M' (jq_mem M'))
    rw [ModularCurve.qExpand_one_apply] at hx0
    exact (ModularCurve.FullLevel.Diamond.mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker q M' hqM' ℓg hℓg hℓg12 hℓgM'
      ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ _ hx0).2 ⟨_, hjqK⟩ rfl γ hγq hγ0 τ hatt

  have hmapBt : (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))}).map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt) = Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapB₀ : (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))}).map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀) = Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hdim : Ring.KrullDimLE 1 (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) := by
    have h3 := (hB₀fib (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})).2.2 1
    rw [hmapBt, hmapB₀] at h3
    exact h3 hR2c
  have hπB₀ne : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩ ≠ 0 := hM2b.ne_zero
  haveI hprime : (Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}).IsPrime := (Ideal.span_singleton_prime hπB₀ne).mpr hM2b
  have hdom : IsDomain (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) := Ideal.Quotient.isDomain _
  have hnorm : IsIntegrallyClosed (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) :=
    ModularCurve.FullLevel.Diamond.AuxLevel.isIntegrallyClosed_invariants_quotient_of_rigidChart_linkedScalars_of_eq_two_of_dvd q hq2 M' ℓg hℓg hℓg12 hℓgM' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ξ H₁ hH₁ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends hqM' hA hW hR₀ hdvr hunif hhens hres hκ hℓ hℓ3 hℓq hℓM' hζ₀ hϖtA hϖt hKb hϖb hϖb0 htame hξ hKℓ hjℓ hϖt' hy hϖy hss hover hOrbit hS1 hn1 hnq hγ₀Γ hγ₀Γ0 hτ₀ hτ₀W hm1 hm hζc hζcprim hjC ha₀y hR7 hR9 hR10 hn G hG K₀ hK₀ B₀ hB₀ W₀' hW₀'

  haveI := hR2a
  haveI hsm : Algebra.Smooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := {}
  haveI hBtic : IsIntegrallyClosed ↥Bt := Algebra.Smooth.isIntegrallyClosed_of_isDomain ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt
  haveI : IsIntegrallyClosed ↥B₀ := hB₀normal hBtic
  haveI : Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ := hB₀ft
  haveI : FaithfulSMul ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ b := by
      rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Kℓ a, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Kℓ b, hab]
    rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ b] at h1
    exact IsFractionRing.injective ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ((algebraMap ↥k₀ ↥Kℓ).injective h1)
  haveI : CharZero ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := inferInstance

  have h0 := ModularCurve.transcendental_coeffEmb_jq ↥k₀ M'
  have h1 : Transcendental ↥k₀ (coeffEmb ↥k₀ jq : LaurentSeries ↥k₀) :=
    (transcendental_algebraMap_iff (R := ↥k₀) (S := ↥(laurentBaseChange ↥k₀ (modularFunctionFieldFull M')))
      (A := LaurentSeries ↥k₀) Subtype.val_injective).mpr h0
  have h3 : Transcendental ↥k₀ (algebraMap ↥B₀ ↥Kℓ ⟨_, hjB₀⟩) :=
    (transcendental_algebraMap_iff (R := ↥k₀) (S := ↥Kℓ) (A := LaurentSeries ↥k₀) Subtype.val_injective).mp h1
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField ↥k₀
    (q ^ 2 * M') H₁
  rw [← hKℓ] at hcurve hess
  haveI := hcurve
  haveI := hess
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin ↥k₀ {algebraMap ↥B₀ ↥Kℓ ⟨_, hjB₀⟩}) ↥Kℓ :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType h3

  have hfib := Algebra.FormallySmooth.residueField_fiber_of_isIntegrallyClosed_quotient_of_transcendental
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hunif hres ↥B₀ ↥k₀ ↥Kℓ Subtype.val_injective ⟨_, hjB₀⟩ h3 hfin hdom hnorm hdim
  exact (hB₀smooth hflat hfib).formallySmooth

end S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_formallySmooth_invariants_of_rigidChart_linkedScalars_of_eq_two_of_dvd (solution)
