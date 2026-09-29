-- Prove2me | solution 1 for ModularCurve.isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/78b021e1-b257-5c5b-ba76-49057cb236a6

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
import Theorems.Thm_ModularCurve_finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.FullLevel.instAddCommGroupJac ModularCurve.FullLevel.instFintypeIdx ModularCurve.FullLevel.instMulActionAlgEquivRatAlgebraicClosureIdx ModularCurve.FullLevel.instDecidableEqIdx AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar"
p2m_attr_erase "instance" "ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.FullLevel.coe_diagOneElem ModularCurve.FullLevel.Jac.eval_neg"
p2m_attr_erase "simp" "ModularCurve.FullLevel.Jac.eval_zsmul ModularCurve.FullLevel.Jac.mapIdx_eval ModularCurve.FullLevel.Idx.val_pow ModularCurve.FullLevel.Idx.val_mk ModularCurve.FullLevel.Idx.val_smul ModularCurve.FullLevel.diagJac_eval ModularCurve.FullLevel.Jac.eval_add ModularCurve.FullLevel.Jac.eval_nsmul ModularCurve.FullLevel.Jac.eval_sub ModularCurve.FullLevel.slJac_eval ModularCurve.FullLevel.Jac.eval_zero ModularCurve.FullLevel.Jac.eval_mk ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ 𝔔)
    [Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)]
    (halg : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) p =
      AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K₀) j₀ p)
    [Algebra (Localization.AtPrime (𝔔.under (Polynomial A))) (Localization.AtPrime 𝔔)]
    [Localization.AtPrime.IsLiesOverAlgebra (𝔔.under (Polynomial A)) 𝔔] :
    Algebra.IsSeparable (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField := by
  classical
  have hqprime : q.Prime := Fact.out
  haveI : CharP (IsLocalRing.ResidueField A) q := by
    apply (CharP.charP_iff_prime_eq_zero hqprime).mpr
    have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr hAq
    rwa [map_natCast] at h3

  obtain ⟨Θ, hΘinj, hΘA, hΘj, zM, hΘbM⟩ := ModularCurve.exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
    q M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ 𝔔 h𝔔 hϖ𝔔
  obtain ⟨hfin, hdeg⟩ := ModularCurve.finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
    q M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ 𝔔 h𝔔 hϖ𝔔 halg

  let φ : (𝔔.under (Polynomial A)).ResidueField →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    Θ.comp (algebraMap (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField)
  have hφinj : Function.Injective φ :=
    hΘinj.comp (algebraMap (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField).injective

  let ψ₀ : Polynomial A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    (Polynomial.aeval (jqModC (IsLocalRing.ResidueField A))).toRingHom.comp (Polynomial.mapRingHom (IsLocalRing.residue A))
  have hψ₀C : ∀ a : A, ψ₀ (Polynomial.C a) = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) := by
    intro a; simp [ψ₀]
  have hψ₀X : ψ₀ Polynomial.X = jqModC (IsLocalRing.ResidueField A) := by simp [ψ₀]
  have hΘO : ∀ p : Polynomial A,
      Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) p)) = ψ₀ p := by
    intro p
    have key : Θ.comp ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField).comp (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀))) = ψ₀ := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [hψ₀C, RingHom.comp_apply, RingHom.comp_apply, halg, Polynomial.C_eq_algebraMap, AlgHom.commutes, hΘA]
      · rw [hψ₀X, RingHom.comp_apply, RingHom.comp_apply, halg, polynomialToChartFin_X, hΘj]
    exact congrArg (fun g : Polynomial A →+* LaurentSeries (IsLocalRing.ResidueField A) => g p) key
  have hφO : ∀ p : Polynomial A, φ (algebraMap (Polynomial A) (𝔔.under (Polynomial A)).ResidueField p) = ψ₀ p := by
    intro p
    show Θ (algebraMap (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField
      (algebraMap (Polynomial A) (𝔔.under (Polynomial A)).ResidueField p)) = ψ₀ p
    rw [← IsScalarTower.algebraMap_apply (Polynomial A) (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField,
      IsScalarTower.algebraMap_apply (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField]
    exact hΘO p
  have hψ₀E₀ : ∀ p : Polynomial A, ψ₀ p ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    intro p
    exact IntermediateField.algebra_adjoin_le_adjoin (IsLocalRing.ResidueField A) _ (Polynomial.aeval_mem_adjoin_singleton _ _)

  have hφc : ∀ c : IsLocalRing.ResidueField A, ∃ x, φ x = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact ⟨algebraMap (Polynomial A) _ (Polynomial.C a), by rw [hφO, hψ₀C]⟩

  have hφE₀ : ∀ x, φ x ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial A ⧸ 𝔔.under (Polynomial A)) x
    obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨pb, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [map_div₀, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply (Polynomial A) (Polynomial A ⧸ 𝔔.under (Polynomial A)) (𝔔.under (Polynomial A)).ResidueField,
      ← IsScalarTower.algebraMap_apply (Polynomial A) (Polynomial A ⧸ 𝔔.under (Polynomial A)) (𝔔.under (Polynomial A)).ResidueField,
      hφO, hφO]
    exact div_mem (hψ₀E₀ pa) (hψ₀E₀ pb)
  have hE₀φ : ∀ y, y ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) → ∃ x, φ x = y := by
    let F₁ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) := Subfield.toIntermediateField φ.fieldRange (fun c => by
      obtain ⟨x, hx⟩ := hφc c
      exact ⟨x, hx⟩)
    have hle : IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) ≤ F₁ := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨algebraMap (Polynomial A) _ Polynomial.X, by rw [hφO, hψ₀X]⟩
    intro y hy
    exact RingHom.mem_fieldRange.mp (hle hy)

  let i₀ : (𝔔.under (Polynomial A)).ResidueField →+* ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) := φ.codRestrict (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) hφE₀
  have hi₀ : Function.Bijective i₀ := by
    refine ⟨fun a b h => hφinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hE₀φ y y.2
    exact ⟨x, Subtype.ext hx⟩
  let i : (𝔔.under (Polynomial A)).ResidueField ≃+* ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) := RingEquiv.ofBijective i₀ hi₀
  have hival : ∀ x, ((i x : ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))))) : LaurentSeries (IsLocalRing.ResidueField A)) = φ x := fun _ => rfl

  let F₂ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) := Subfield.toIntermediateField Θ.fieldRange (fun c => by
    obtain ⟨x, hx⟩ := hφc c
    exact ⟨_, hx⟩)
  have hmemF₂ : ∀ y : LaurentSeries (IsLocalRing.ResidueField A), y ∈ F₂ ↔ ∃ x, Θ x = y := fun y => RingHom.mem_fieldRange
  have hE₀F₂ : IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) ≤ F₂ := by
    intro y hy
    obtain ⟨x, hx⟩ := hE₀φ y hy
    exact (hmemF₂ y).mpr ⟨_, hx⟩
  have hMF₂ : modularFunctionFieldC (IsLocalRing.ResidueField A) M' ≤ F₂ := by
    rw [modularFunctionFieldC, IntermediateField.adjoin_le_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact (hmemF₂ _).mpr ⟨_, hΘj⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hmemF₂ _).mpr ⟨_, hΘbM⟩
  have hE₀M : IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))) ≤ modularFunctionFieldC (IsLocalRing.ResidueField A) M' :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

  let j₀' : 𝔔.ResidueField →+* ↥(IntermediateField.extendScalars hE₀F₂) :=
    Θ.codRestrict (IntermediateField.extendScalars hE₀F₂)
      (fun x => (IntermediateField.mem_extendScalars hE₀F₂).mpr ((hmemF₂ _).mpr ⟨x, rfl⟩))
  have hj₀' : Function.Bijective j₀' := by
    refine ⟨fun a b h => hΘinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hmemF₂ _).mp ((IntermediateField.mem_extendScalars hE₀F₂).mp y.2)
    exact ⟨x, Subtype.ext hx⟩
  let jE : 𝔔.ResidueField ≃+* ↥(IntermediateField.extendScalars hE₀F₂) := RingEquiv.ofBijective j₀' hj₀'
  have hjval : ∀ x, ((jE x : ↥(IntermediateField.extendScalars hE₀F₂)) : LaurentSeries (IsLocalRing.ResidueField A)) = Θ x := fun _ => rfl
  have hc : (algebraMap ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀F₂)).comp i.toRingHom =
      jE.toRingHom.comp (algebraMap (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField) := by
    refine RingHom.ext (fun x => ?_)
    apply Subtype.ext
    rfl

  have hrank : Module.finrank (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField =
      Module.finrank ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀F₂) :=
    Algebra.finrank_eq_of_equiv_equiv i jE hc
  haveI : Module.Finite (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField := hfin
  have hpos : 0 < Module.finrank (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField := Module.finrank_pos
  haveI : FiniteDimensional ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀F₂) :=
    Module.finite_of_finrank_pos (by rw [← hrank]; exact hpos)
  have hψ : Module.finrank ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀M) = dedekindPsi M' := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hE₀M]
    exact ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi (IsLocalRing.ResidueField A) M' q hqM'
  have hle : IntermediateField.extendScalars hE₀M ≤ IntermediateField.extendScalars hE₀F₂ :=
    (IntermediateField.extendScalars_le_extendScalars_iff hE₀M hE₀F₂).mpr hMF₂
  have heq : IntermediateField.extendScalars hE₀M = IntermediateField.extendScalars hE₀F₂ :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [← hrank, hψ]; exact hdeg)
  have hF₂M : ∀ y : LaurentSeries (IsLocalRing.ResidueField A), y ∈ F₂ → y ∈ modularFunctionFieldC (IsLocalRing.ResidueField A) M' := by
    intro y hy
    have h1 : y ∈ IntermediateField.extendScalars hE₀F₂ := (IntermediateField.mem_extendScalars hE₀F₂).mpr hy
    rw [← heq] at h1
    exact (IntermediateField.mem_extendScalars hE₀M).mp h1

  have hT : IntermediateField.extendScalars hE₀F₂ =
      IntermediateField.adjoin ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ({jqNModC (IsLocalRing.ResidueField A) M'} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    apply IntermediateField.restrictScalars_injective (IsLocalRing.ResidueField A)
    have hAA : IntermediateField.restrictScalars (IsLocalRing.ResidueField A)
        (IntermediateField.adjoin ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ({jqNModC (IsLocalRing.ResidueField A) M'} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) =
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A), jqNModC (IsLocalRing.ResidueField A) M'} : Set (LaurentSeries (IsLocalRing.ResidueField A))) :=
      IntermediateField.adjoin_simple_adjoin_simple (IsLocalRing.ResidueField A) (jqModC (IsLocalRing.ResidueField A)) (jqNModC (IsLocalRing.ResidueField A) M')
    refine Eq.trans ?_ hAA.symm
    ext y
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_extendScalars]
    exact ⟨hF₂M y, fun hy => hMF₂ hy⟩
  have hsepT : Algebra.IsSeparable ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))))
      ↥(IntermediateField.adjoin ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ({jqNModC (IsLocalRing.ResidueField A) M'} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2
      (ModularCurve.isSeparable_jqNModC_of_good (IsLocalRing.ResidueField A) M' q hqM')
  have hsep2 : Algebra.IsSeparable ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀F₂) := by
    rw [hT]; exact hsepT

  have hc' : (algebraMap (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField).comp i.symm.toRingHom =
      jE.symm.toRingHom.comp (algebraMap ↥(IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) ↥(IntermediateField.extendScalars hE₀F₂)) := by
    ext y
    apply jE.injective
    show jE (algebraMap _ 𝔔.ResidueField (i.symm y)) = jE (jE.symm (algebraMap _ _ y))
    rw [jE.apply_symm_apply]
    have := congrArg (fun g : (𝔔.under (Polynomial A)).ResidueField →+* ↥(IntermediateField.extendScalars hE₀F₂) => g (i.symm y)) hc
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    exact this.symm
  exact Algebra.IsSeparable.of_equiv_equiv i.symm jE.symm hc'

end S_ModularCurve_isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd (solution)
