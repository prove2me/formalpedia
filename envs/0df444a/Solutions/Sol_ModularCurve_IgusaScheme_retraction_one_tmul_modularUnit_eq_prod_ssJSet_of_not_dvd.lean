-- Prove2me | solution 1 for ModularCurve.IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/948a6aa1-1048-524d-aebd-cc6b4e5b2144

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

noncomputable section

namespace OggComp

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def tensorAddHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => F x * G b) (fun b b' => by simp only [map_add, mul_add]))
      (fun x x' => by ext b; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun r x b => by
      have key := RingHom.congr_fun (ringHom_ext_zp (p := p) (F.comp (algebraMap ℤp A)) (G.comp (algebraMap ℤp M))) r
      simp only [RingHom.coe_comp, Function.comp_apply] at key
      show F (r • x) * G b = F x * G (r • b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, key]
      ring)

theorem tensorAddHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorAddHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b := by
  unfold tensorAddHom
  rw [TensorProduct.liftAddHom_tmul]
  rfl

def tensorRingHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+* L :=
  { tensorAddHom (p := p) F G with
    map_one' := by
      show tensorAddHom (p := p) F G 1 = 1
      rw [Algebra.TensorProduct.one_def, tensorAddHom_tmul, map_one, map_one, one_mul]
    map_mul' := fun s t => by
      show tensorAddHom (p := p) F G (s * t) = tensorAddHom (p := p) F G s * tensorAddHom (p := p) F G t
      induction s using TensorProduct.induction_on with
      | zero => rw [zero_mul, map_zero, zero_mul]
      | tmul x b =>
        induction t using TensorProduct.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | tmul x' b' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, tensorAddHom_tmul, tensorAddHom_tmul, tensorAddHom_tmul, map_mul,
            map_mul]
          ring
        | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      | add s₁ s₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂] }

theorem tensorRingHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorRingHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b :=
  tensorAddHom_tmul (p := p) F G x b

theorem isIntegral_of_mem (M : ℕ) [NeZero M] (κ : Type) [Field κ] [Algebra ℤp κ]
    (K : Subalgebra κ (κ ⊗[ℤp] ↥(chartAlgFin M p)))
    (hK : (1 : κ) ⊗ₜ[ℤp] jChartFin M p ∈ K) (z : κ ⊗[ℤp] ↥(chartAlgFin M p)) :
    IsIntegral K z := by
  induction z using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | add x y hx hy => exact hx.add hy
  | tmul x b =>
    have hxb : x ⊗ₜ[ℤp] b = algebraMap κ (κ ⊗[ℤp] ↥(chartAlgFin M p)) x * ((1 : κ) ⊗ₜ[ℤp] b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hxb]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_algebraMap (R := K) (x := ⟨_, K.algebraMap_mem x⟩)
    ·
      obtain ⟨P, hPm, hP⟩ := (mem_chartAlg_iff M p).mp b.2

      let incl : ↥(Algebra.adjoin ℤp {jFull M}) →ₐ[ℤp] ↥(chartAlgFin M p) :=
        Subalgebra.inclusion (adjoin_le_chartAlg M p {jFull M})
      let ρₐ : ↥(Algebra.adjoin ℤp {jFull M}) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin M p) :=
        (Algebra.TensorProduct.includeRight : ↥(chartAlgFin M p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin M p)).comp incl

      have hρK : ∀ a : ↥(Algebra.adjoin ℤp {jFull M}), ρₐ a ∈ K := by
        rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          have : ρₐ ⟨jFull M, Algebra.subset_adjoin rfl⟩ = (1 : κ) ⊗ₜ[ℤp] jChartFin M p := rfl
          rw [this]
          exact hK
        | algebraMap r =>
          have : (⟨algebraMap ℤp ↥(modularFunctionFieldFull M) r, Subalgebra.algebraMap_mem _ r⟩ :
              ↥(Algebra.adjoin ℤp {jFull M})) = algebraMap ℤp _ r := rfl
          rw [this, AlgHom.commutes, IsScalarTower.algebraMap_apply ℤp κ (κ ⊗[ℤp] ↥(chartAlgFin M p))]
          exact K.algebraMap_mem _
        | add y y' hy hy' h h' =>
          have : (⟨y + y', add_mem hy hy'⟩ : ↥(Algebra.adjoin ℤp {jFull M})) = ⟨y, hy⟩ + ⟨y', hy'⟩ := rfl
          rw [this, map_add]
          exact K.add_mem h h'
        | mul y y' hy hy' h h' =>
          have : (⟨y * y', mul_mem hy hy'⟩ : ↥(Algebra.adjoin ℤp {jFull M})) = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
          rw [this, map_mul]
          exact K.mul_mem h h'

      have hroot : (P.map ρₐ.toRingHom).eval ((1 : κ) ⊗ₜ[ℤp] b) = 0 := by
        have h1 : P.eval₂ incl.toRingHom b = 0 := by
          apply Subtype.val_injective
          have := Polynomial.hom_eval₂ P incl.toRingHom (chartAlgFin M p).val.toRingHom b
          have hcomp : (chartAlgFin M p).val.toRingHom.comp incl.toRingHom =
              algebraMap ↥(Algebra.adjoin ℤp {jFull M}) ↥(modularFunctionFieldFull M) :=
            RingHom.ext fun _ => rfl
          rw [hcomp] at this
          exact this.trans hP
        have h2 := Polynomial.hom_eval₂ P incl.toRingHom
          (Algebra.TensorProduct.includeRight : ↥(chartAlgFin M p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin M p)).toRingHom b
        rw [h1, map_zero] at h2
        rw [Polynomial.eval_map]
        exact h2.symm

      have hlifts : P.map ρₐ.toRingHom ∈ Polynomial.lifts (algebraMap K (κ ⊗[ℤp] ↥(chartAlgFin M p))) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map, Subalgebra.setRange_algebraMap]
        exact hρK _
      obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPm.map _)
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQmap]
      exact hroot

theorem jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have := order_jqModC K
  rw [h, HahnSeries.order_zero] at this
  norm_num at this

theorem jqModC_ne_C (K : Type*) [Field K] (a : K) : jqModC K ≠ HahnSeries.C a := by
  intro h
  have h1 : (jqModC K).coeff (-1) ≠ 0 := by
    have := (mt HahnSeries.coeff_order_eq_zero.mp (jqModC_ne_zero K))
    rwa [order_jqModC] at this
  rw [h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℤ) ≠ 0)] at h1
  exact h1 rfl

theorem eval₂_C_ne_zero {K : Type*} [Field K] (y : LaurentSeries K) (hy : y.order < 0)
    (P : Polynomial K) (hP : P ≠ 0) : P.eval₂ HahnSeries.C y ≠ 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [HahnSeries.order_zero] at hy
    exact lt_irrefl _ hy
  have hord : ∀ n : ℕ, (y ^ n).order = n * y.order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hy0) hy0, ih]; push_cast; ring
  set n := P.natDegree with hn
  have hlead : P.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP

  intro h
  have hc := congrArg (fun s : LaurentSeries K => s.coeff (n * y.order)) h
  simp only [HahnSeries.coeff_zero] at hc
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at hc
  · refine mul_ne_zero hlead ?_ hc
    rw [← hord n]
    exact (mt HahnSeries.coeff_order_eq_zero.mp (pow_ne_zero n hy0))
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
    rw [hord i]
    have : (i : ℤ) < n := by exact_mod_cast hi
    nlinarith

section Main

variable (N : ℕ) [NeZero N]
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem false_of_one_tmul_j_eq_pow
    (g₀ : ↥(chartAlgFin N p) →+* LaurentSeries κ) (hg₀ : g₀ (jChartFin N p) = jqModC κ)
    (s : κ ⊗[ℤp] ↥(chartAlgFin N p)) (hs : (1 : κ) ⊗ₜ[ℤp] jChartFin N p = s ^ p) : False := by
  let χ : κ ⊗[ℤp] ↥(chartAlgFin N p) →+* LaurentSeries κ := tensorRingHom (p := p) HahnSeries.C g₀
  have hχj : χ ((1 : κ) ⊗ₜ[ℤp] jChartFin N p) = jqModC κ := by
    show tensorRingHom (p := p) _ _ _ = _
    rw [tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC κ := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    exact jqModC_ne_zero κ hpow.symm
  have hord : ∀ n : ℕ, (x ^ n).order = n * x.order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hx0) hx0, ih]; push_cast; ring
  have h := congrArg HahnSeries.order hpow
  rw [hord, order_jqModC] at h
  have hdvd : (p : ℤ) ∣ 1 := ⟨-x.order, by linarith⟩
  have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem one_tmul_natCast_mul {M : Type*} [CommRing M] [Algebra ℤp M] (c : M) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : M) * c) = 0 := by
  rw [show ((p : ℕ) : M) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem ι_jChartFin
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) :
    ι (jChartFin N p) = jChartFin (N * p) p := by
  have hj1 : (((ι (jChartFin N p) : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := by rw [hι]; rfl
  have hj2 : (((jChartFin (N * p) p : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := rfl
  exact Subtype.ext (Subtype.ext (hj1.trans hj2.symm))

theorem ker_retraction_mem_minimalPrimes (hpN : ¬ p ∣ N) [IsAlgClosed κ]
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hιj : ι (jChartFin N p) = jChartFin (N * p) p)
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z) :
    RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) :=
    (isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N p hpN κ).1
  let φ : κ ⊗[ℤp] ↥(chartAlgFin N p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) ι
  haveI hP : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hK : (1 : κ) ⊗ₜ[ℤp] jChartFin (N * p) p ∈ φ.range :=
φ.mem_range.2 ⟨(1 : κ) ⊗ₜ[ℤp] jChartFin N p, by
      show Algebra.TensorProduct.map (AlgHom.id κ κ) ι _ = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιj]⟩
  haveI : Algebra.IsIntegral ↥φ.range (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) :=
    ⟨fun z => isIntegral_of_mem (N * p) κ φ.range hK z⟩
  have hcomap : (RingHom.ker σ₀.toRingHom).comap
      (algebraMap ↥φ.range (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨t, ht⟩ hmem
    obtain ⟨s, rfl⟩ := φ.mem_range.1 ht
    rw [Ideal.mem_comap, RingHom.mem_ker] at hmem
    change σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι s) = 0 at hmem
    rw [h0] at hmem
    subst hmem
    rw [Ideal.mem_bot]
    exact Subtype.ext (map_zero φ)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) ≤ RingHom.ker σ₀.toRingHom)
  suffices hQP : Q = RingHom.ker σ₀.toRingHom by rw [← hQP]; exact hQ
  by_contra hne
  haveI : Q.IsPrime := hQ.1.1
  obtain ⟨-, x, hxP, hxQ⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hQle hne)
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥φ.range) hQle ⟨hxP, hxQ⟩
    (Algebra.IsIntegral.isIntegral x)
  rw [hcomap] at hlt
  exact not_lt_bot hlt

theorem map_id_bijective {M : Type*} [CommRing M] [Algebra ℤp M] (w : M ≃ₐ[ℤp] M) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom) := by
  have h1 : ∀ z, Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) w.symm.toAlgHom z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x c =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have h2 : ∀ z, Algebra.TensorProduct.map (AlgHom.id κ κ) w.symm.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x c =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

theorem comap_mem_minimalPrimes_of_bijective {T : Type*} [CommRing T] (f : T →+* T)
    (hf : Function.Bijective f) {P : Ideal T} (hP : P ∈ minimalPrimes T) : P.comap f ∈ minimalPrimes T := by
  have h := Ideal.minimalPrimes_comap_of_surjective hf.2 hP
  rwa [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot f).mp hf.1] at h

theorem eq_zero_of_mem_ssJSet_of_lt_five' {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] (hq : q < 5) (a : K) (ha : a ∈ ssJSet q K) : a = 0 := by
  have hqp : q.Prime := Fact.out
  have ha2 := pow_q_sq_eq_self_of_mem_ssJSet q ha
  interval_cases q
  · exact absurd hqp (by decide)
  · exact absurd hqp (by decide)
  · exact eq_zero_of_mem_ssJSet_two a ha ha2
  · exact eq_zero_of_mem_ssJSet_three a ha ha2
  · exact absurd hqp (by decide)

theorem jWidth_div_pos {K : Type*} [Field K] [DecidableEq K] (a : K) : 0 < 12 / jWidth a := by
  have h6 : jWidth a ≤ 6 := Nat.le_of_dvd (by norm_num) (jWidth_dvd_six a)
  exact Nat.div_pos (by omega) (jWidth_pos a)

theorem coe_mul_w_eq (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (v : ↥(chartAlgFin (N * p) p))
    (hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p) :
    (((v * w v : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      coeffMap (Int.castRingHom ℚ) (HahnSeries.single 0 ((p : ℤ) ^ 12)) := by
  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p) := by
    rw [← hv]; exact (v : ↥(modularFunctionFieldFull (N * p))).2
  have hvF : (v : ↥(modularFunctionFieldFull (N * p))) = ⟨modularUnitSeries p, hmem⟩ := Subtype.ext hv
  have h3 := ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd N p hpN hmem
  rw [← hvF] at h3
  have hne : modularUnitSeries p ≠ 0 := modularUnitSeries_ne_zero p

  have hR : coeffMap (Int.castRingHom ℚ) (HahnSeries.single 0 ((p : ℤ) ^ 12)) = (p : LaurentSeries ℚ) ^ 12 := by
    have h1 : (HahnSeries.single 0 ((p : ℤ) ^ 12) : LaurentSeries ℤ) = (p : LaurentSeries ℤ) ^ 12 := by
      rw [← HahnSeries.C_apply, map_pow, map_natCast]
    rw [h1, map_pow, map_natCast]
  rw [hR]
  push_cast
  rw [hw v, h3, hv, ← HahnSeries.C_mul_eq_smul, map_pow, map_natCast, mul_left_comm, mul_inv_cancel₀ hne, mul_one]

theorem ker_ne_ker_comp
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hιj : ι (jChartFin N p) = jChartFin (N * p) p)
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (hjqN : θ 0 (ι (jChartFin N p)) = jqModC κ)
    (hkill : ∀ c, θ 0 c = 0 → σ₀ ((1 : κ) ⊗ₜ[ℤp] c) = 0) :
    RingHom.ker σ₀.toRingHom ≠
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)).toRingHom := by
  intro hEq
  have hI1 : ∀ c, θ 1 c = 0 → σ₀ ((1 : κ) ⊗ₜ[ℤp] c) = 0 := fun c hc => by
    have h' : ((1 : κ) ⊗ₜ[ℤp] c) ∈
        RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)).toRingHom := by
      rw [RingHom.mem_ker]
      show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom ((1 : κ) ⊗ₜ[ℤp] c)) = 0
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply]
      exact hkill (w c) (by rw [← hθ1]; exact hc)
    rw [← hEq, RingHom.mem_ker] at h'
    exact h'
  have hu : θ 1 (jChartFin (N * p) p - (w.symm (jChartFin (N * p) p)) ^ p) = 0 := by
    rw [hθ1, map_sub, map_pow, AlgEquiv.apply_symm_apply, ← hιj, map_sub, map_pow, hfrob, sub_self]
  have h := hI1 _ hu
  have hl : σ₀ ((1 : κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = (1 : κ) ⊗ₜ[ℤp] jChartFin N p := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jChartFin N p), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hr : σ₀ ((1 : κ) ⊗ₜ[ℤp] ((w.symm (jChartFin (N * p) p)) ^ p)) =
      (σ₀ ((1 : κ) ⊗ₜ[ℤp] w.symm (jChartFin (N * p) p))) ^ p := by
    rw [← map_pow σ₀, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero, hl, hr] at h
  exact false_of_one_tmul_j_eq_pow N κ ((θ 0).comp ι.toRingHom) hjqN _ h

theorem ker_le_ker_tensorRingHom
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* LaurentSeries κ))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hker0 : RingHom.ker (θ 0) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes)
    (hker1 : RingHom.ker (θ 1) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes)
    (hkill : ∀ c, θ 0 c = 0 → σ₀ ((1 : κ) ⊗ₜ[ℤp] c) = 0)
    (hall : minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) =
      {RingHom.ker σ₀.toRingHom,
        RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)).toRingHom}) :
    RingHom.ker σ₀.toRingHom ≤ RingHom.ker (tensorRingHom (p := p) HahnSeries.C (θ 0)) := by
  haveI : (RingHom.ker (tensorRingHom (p := p) HahnSeries.C (θ 0))).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) ≤
      RingHom.ker (tensorRingHom (p := p) HahnSeries.C (θ 0)))
  have hQ' : Q ∈ ({RingHom.ker σ₀.toRingHom,
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)).toRingHom} :
      Set (Ideal (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)))) := hall ▸ hQ
  rcases hQ' with hQ0 | hQ1
  · rw [← hQ0]; exact hQle
  · exfalso
    rw [Set.mem_singleton_iff] at hQ1
    rw [hQ1] at hQle
    apply hne
    have h10 : RingHom.ker (θ 1) ≤ RingHom.ker (θ 0) := fun c hc => by
      have hmem : ((1 : κ) ⊗ₜ[ℤp] c) ∈ RingHom.ker (tensorRingHom (p := p) HahnSeries.C (θ 0)) := by
        refine hQle ?_
        rw [RingHom.mem_ker]
        show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom ((1 : κ) ⊗ₜ[ℤp] c)) = 0
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply]
        exact hkill (w c) (by rw [← hθ1]; exact RingHom.mem_ker.mp hc)
      rw [RingHom.mem_ker, tensorRingHom_tmul, map_one, one_mul] at hmem
      exact RingHom.mem_ker.mpr hmem
    exact le_antisymm (hker0.2 ⟨hker1.1.1, hker1.1.2⟩ h10) h10

theorem eq_zero_of_reading_eq_zero (hpN : ¬ p ∣ N) [IsAlgClosed κ]
    (Θ' : κ ⊗[ℤp] ↥(chartAlgFin N p) →+* LaurentSeries κ)
    (hC : ∀ a : κ, Θ' (algebraMap κ (κ ⊗[ℤp] ↥(chartAlgFin N p)) a) = HahnSeries.C a)
    (hj : (Θ' ((1 : κ) ⊗ₜ[ℤp] jChartFin N p)).order < 0)
    (s : κ ⊗[ℤp] ↥(chartAlgFin N p)) (hs : Θ' s = 0) : s = 0 := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) :=
    (isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N p hpN κ).1

  obtain ⟨K, hKdef⟩ : ∃ K : Subalgebra κ (κ ⊗[ℤp] ↥(chartAlgFin N p)),
      K = Algebra.adjoin κ {(1 : κ) ⊗ₜ[ℤp] jChartFin N p} := ⟨_, rfl⟩
  have hjK : (1 : κ) ⊗ₜ[ℤp] jChartFin N p ∈ K := by
    rw [hKdef]; exact Algebra.subset_adjoin (Set.mem_singleton _)
  haveI : Algebra.IsIntegral ↥K (κ ⊗[ℤp] ↥(chartAlgFin N p)) := ⟨fun z => isIntegral_of_mem N κ K hjK z⟩
  haveI : (RingHom.ker Θ').IsPrime := RingHom.ker_isPrime _
  have hcomap : (RingHom.ker Θ').comap (algebraMap ↥K (κ ⊗[ℤp] ↥(chartAlgFin N p))) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨k, hk⟩ hk0
    rw [Ideal.mem_comap, RingHom.mem_ker] at hk0
    change Θ' k = 0 at hk0
    have hk' : k ∈ Algebra.adjoin κ {(1 : κ) ⊗ₜ[ℤp] jChartFin N p} := hKdef ▸ hk
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hk'
    obtain ⟨P, rfl⟩ := hk'
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at hk0
    have hPC : Θ'.comp (algebraMap κ (κ ⊗[ℤp] ↥(chartAlgFin N p))) = HahnSeries.C := RingHom.ext hC
    rw [hPC] at hk0
    have hP0 : P = 0 := by
      by_contra hP
      exact eval₂_C_ne_zero _ hj P hP hk0
    rw [Ideal.mem_bot]
    apply Subtype.ext
    show Polynomial.aeval _ P = ((0 : ↥K) : κ ⊗[ℤp] ↥(chartAlgFin N p))
    rw [hP0, map_zero]
    rfl
  have hbot : RingHom.ker Θ' = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ↥K) hcomap
  have : s ∈ RingHom.ker Θ' := RingHom.mem_ker.mpr hs
  rw [hbot, Ideal.mem_bot] at this
  exact this

set_option maxHeartbeats 16000000 in
theorem main (hpN : ¬ p ∣ N) [IsAlgClosed κ] [DecidableEq κ]
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (v : ↥(chartAlgFin (N * p) p))
    (hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p) :
    σ₀ ((1 : κ) ⊗ₜ[ℤp] (w v : ↥(chartAlgFin (N * p) p))) = 0 ∧
    (5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[ℤp] v) =
        ∏ a ∈ S, ((1 : κ) ⊗ₜ[ℤp] jChartFin N p - a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin N p))) ^ (12 / jWidth a)) ∧
    (∀ 𝔭 : Ideal (κ ⊗[ℤp] ↥(chartAlgFin N p)), 𝔭.IsPrime →
      (σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ∈ 𝔭 ↔
        ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[ℤp] jChartFin N p - a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin N p)) ∈ 𝔭)) ∧
    σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ≠ 0 ∧
    (RingHom.ker σ₀ ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)) ∈
        minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker σ₀ ≠ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom))) := by
  have hpp : p.Prime := Fact.out
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) :=
    (isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N p hpN κ).1
  have hιj : ι (jChartFin N p) = jChartFin (N * p) p := ι_jChartFin N ι hι

  let φ : κ ⊗[ℤp] ↥(chartAlgFin N p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) ι
  have hφ : ∀ x b, φ (x ⊗ₜ[ℤp] b) = x ⊗ₜ[ℤp] ι b := fun x b => by
    show Algebra.TensorProduct.map (AlgHom.id κ κ) ι _ = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have h0' : ∀ z, σ₀ (φ z) = z := h0
  clear_value φ
  let ψ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom

  obtain ⟨θ, hθ1, hpin, hne, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N p hpN ι hι w hw κ
  have hker0 : RingHom.ker (θ 0) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert _ _
  have hker1 : RingHom.ker (θ 1) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ rfl

  have hjq : θ 0 (jChartFin (N * p) p) = jqModC κ := by
    rw [hpin (jChartFin (N * p) p) (jqModC ℤ)]
    · show (jqModC ℤ).map (Int.castRingHom κ) = _
      exact map_jqModC _
    · show jq = (jqModC ℤ).map (Int.castRingHom ℚ)
      rw [map_jqModC, jqModC_rat]
  have hjqN : θ 0 (ι (jChartFin N p)) = jqModC κ := by rw [hιj, hjq]

  have hPmin : RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) :=
    ker_retraction_mem_minimalPrimes N κ hpN ι hιj σ₀ h0
  have hP'eq : RingHom.ker (σ₀.comp ψ).toRingHom = (RingHom.ker σ₀.toRingHom).comap ψ.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have hP'min : RingHom.ker (σ₀.comp ψ).toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) := by
    rw [hP'eq]; exact comap_mem_minimalPrimes_of_bijective ψ.toRingHom (map_id_bijective κ w) hPmin

  have hI0 : Ideal.map (Algebra.TensorProduct.includeRight :
      ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) (RingHom.ker (θ 0)) ≤
      RingHom.ker σ₀.toRingHom :=
    (map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd N p hpN κ ι hι w hw σ₀ h0 _ hker0).mpr
      (by rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self])
  have hkill : ∀ c, θ 0 c = 0 → σ₀ ((1 : κ) ⊗ₜ[ℤp] c) = 0 := fun c hc => by
    have h := hI0 (Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight (RingHom.mem_ker.mpr hc))
    rw [RingHom.mem_ker] at h
    exact h

  have hPne := ker_ne_ker_comp N κ ι hιj w σ₀ h0 θ hθ1 hfrob hjqN hkill
  obtain ⟨hfin, hcard⟩ := finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd N p hpN κ
  have hall : minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) =
      {RingHom.ker σ₀.toRingHom, RingHom.ker (σ₀.comp ψ).toRingHom} :=
    (Set.eq_of_subset_of_ncard_le
      (Set.insert_subset_iff.mpr ⟨hPmin, Set.singleton_subset_iff.mpr hP'min⟩)
      (by rw [hcard, Set.ncard_pair hPne]) hfin).symm

  let Θ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →+* LaurentSeries κ :=
    tensorRingHom (p := p) HahnSeries.C (θ 0)
  have hΘ : ∀ x c, Θ (x ⊗ₜ[ℤp] c) = HahnSeries.C x * θ 0 c := tensorRingHom_tmul (p := p) _ _
  have hPle : RingHom.ker σ₀.toRingHom ≤ RingHom.ker Θ :=
    ker_le_ker_tensorRingHom N κ w σ₀ θ hθ1 hne hker0 hker1 hkill hall
  clear_value Θ
  have hfac : ∀ z, Θ z = Θ (φ (σ₀ z)) := fun z => by
    have hz : z - φ (σ₀ z) ∈ RingHom.ker σ₀.toRingHom := by
      rw [RingHom.mem_ker]
      show σ₀ (z - φ (σ₀ z)) = 0
      rw [map_sub σ₀, h0', sub_self]
    have := hPle hz
    rw [RingHom.mem_ker, map_sub Θ, sub_eq_zero] at this
    exact this
  have hΘφ : ∀ x b, Θ (φ (x ⊗ₜ[ℤp] b)) = HahnSeries.C x * θ 0 (ι b) := fun x b => by rw [hφ, hΘ]

  obtain ⟨Θ', hΘ'def⟩ : ∃ Θ' : κ ⊗[ℤp] ↥(chartAlgFin N p) →+* LaurentSeries κ,
      Θ' = tensorRingHom (p := p) HahnSeries.C ((θ 0).comp ι.toRingHom) := ⟨_, rfl⟩
  have hΘ't : ∀ x b, Θ' (x ⊗ₜ[ℤp] b) = HahnSeries.C x * θ 0 (ι b) := fun x b => by
    rw [hΘ'def, tensorRingHom_tmul]; rfl
  have hΘφ' : ∀ s, Θ (φ s) = Θ' s := fun s => by
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero φ, map_zero Θ, map_zero]
    | tmul x b => rw [hΘφ, hΘ't]
    | add a b ha hb => rw [map_add φ, map_add Θ, map_add, ha, hb]
  have hΘ'j : Θ' ((1 : κ) ⊗ₜ[ℤp] jChartFin N p) = jqModC κ := by rw [hΘ't, map_one, one_mul, hjqN]
  have hΘ'a : ∀ a : κ, Θ' (a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin N p))) = HahnSeries.C a := fun a => by
    rw [hΘ't, map_one, map_one, mul_one]
  have hinj : ∀ s : κ ⊗[ℤp] ↥(chartAlgFin N p), Θ' s = 0 → s = 0 := fun s hs => by
    refine eq_zero_of_reading_eq_zero N κ hpN Θ' (fun a => ?_) ?_ s hs
    · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΘ'a]
    · rw [hΘ'j, order_jqModC]
      norm_num
  have hinj' : ∀ s t : κ ⊗[ℤp] ↥(chartAlgFin N p), Θ' s = Θ' t → s = t := fun s t h =>
    sub_eq_zero.mp (hinj _ ((map_sub Θ' s t).trans (by rw [h, sub_self])))
  have hΘv : Θ ((1 : κ) ⊗ₜ[ℤp] v) = θ 0 v := by rw [hΘ, map_one, one_mul]

  have hθv_small : p < 5 → θ 0 v = jqModC κ ^ (p - 1) := fun hp5 => by
    obtain ⟨x, hxℚ, hxκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five p hp5
    rw [hpin v x (hv.trans hxℚ.symm), hxκ κ]
  have hθv_large : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      θ 0 v = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := fun hp5 S hS => by
    obtain ⟨x, hxℚ, hxκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp5
    rw [hpin v x (hv.trans hxℚ.symm), hxκ κ S hS]
  have hθv0 : θ 0 v ≠ 0 := by
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · rw [hθv_small hp5]; exact pow_ne_zero _ (jqModC_ne_zero κ)
    · rw [hθv_large hp5 (ssJSet_finite p κ).toFinset (fun a => Set.Finite.mem_toFinset _)]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (sub_ne_zero.mpr (jqModC_ne_C κ a))

  have hvw : θ 0 (v * w v) = 0 := by
    rw [hpin (v * w v) _ (coe_mul_w_eq N hpN w hw v hv), coeffMap_single, map_pow, map_natCast,
      CharP.cast_eq_zero, zero_pow (by norm_num), HahnSeries.single_eq_zero]
  have ha : σ₀ ((1 : κ) ⊗ₜ[ℤp] (w v : ↥(chartAlgFin (N * p) p))) = 0 := by
    refine hkill (w v) ?_
    have h := hvw
    rw [map_mul (θ 0)] at h
    exact (mul_eq_zero.mp h).resolve_left hθv0

  have hd : σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ≠ 0 := fun h =>
    hθv0 (by rw [← hΘv, hfac, h, map_zero φ, map_zero Θ])

  have hb : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[ℤp] v) =
        ∏ a ∈ S, ((1 : κ) ⊗ₜ[ℤp] jChartFin N p - a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin N p))) ^ (12 / jWidth a) := by
    intro hp5 S hS
    apply hinj'
    rw [← hΘφ', ← hfac, hΘv, hθv_large hp5 S hS, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_pow Θ', map_sub Θ', hΘ'j, hΘ'a]

  have hb_small : p < 5 → σ₀ ((1 : κ) ⊗ₜ[ℤp] v) = ((1 : κ) ⊗ₜ[ℤp] jChartFin N p) ^ (p - 1) := fun hp5 => by
    have hk : θ 0 (v - ι (jChartFin N p) ^ (p - 1)) = 0 := by
      rw [map_sub, map_pow, hθv_small hp5, hjqN, sub_self]
    have := hkill _ hk
    rw [TensorProduct.tmul_sub, map_sub σ₀, sub_eq_zero] at this
    rw [this, ← h0' (((1 : κ) ⊗ₜ[ℤp] jChartFin N p) ^ (p - 1)), map_pow φ, hφ]
    congr 1
    rw [Algebra.TensorProduct.tmul_pow, one_pow]

  have hc : ∀ 𝔭 : Ideal (κ ⊗[ℤp] ↥(chartAlgFin N p)), 𝔭.IsPrime →
      (σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ∈ 𝔭 ↔
        ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[ℤp] jChartFin N p - a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin N p)) ∈ 𝔭) := by
    intro 𝔭 h𝔭
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp1 : 0 < p - 1 := by have := hpp.two_le; omega
      rw [hb_small hp5]
      constructor
      · intro h
        refine ⟨0, zero_mem_ssJSet_of_lt_five hp5, ?_⟩
        rw [TensorProduct.zero_tmul, sub_zero]
        exact h𝔭.mem_of_pow_mem _ h
      · rintro ⟨a, ha, hmem⟩
        have ha0 : a = 0 := eq_zero_of_mem_ssJSet_of_lt_five' p hp5 a ha
        rw [ha0, TensorProduct.zero_tmul, sub_zero] at hmem
        exact Ideal.pow_mem_of_mem 𝔭 hmem _ hp1
    · have hS : ∀ a, a ∈ (ssJSet_finite p κ).toFinset ↔ a ∈ ssJSet p κ := fun a => Set.Finite.mem_toFinset _
      rw [hb hp5 _ hS]
      haveI := h𝔭
      constructor
      · intro h
        obtain ⟨a, haS, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h
        exact ⟨a, (hS a).mp haS, h𝔭.mem_of_pow_mem _ ha⟩
      · rintro ⟨a, ha, hmem⟩
        rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem ((hS a).mpr ha)]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem 𝔭 hmem _ (jWidth_div_pos a))
  have hk1 : RingHom.ker σ₀.toRingHom = RingHom.ker σ₀ := Ideal.ext fun _ => Iff.rfl
  have hk2 : RingHom.ker (σ₀.comp ψ).toRingHom = RingHom.ker (σ₀.comp ψ) := Ideal.ext fun _ => Iff.rfl
  rw [hk1] at hPmin hPne
  rw [hk2] at hP'min hPne
  exact ⟨ha, hb, hc, hd, hPmin, hP'min, hPne⟩

end Main

end OggComp

end

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))

    (σ₀ : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[κ]
        κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)

    (v : ↥(chartAlgFin (N * p) p))
    (hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p) :

    σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (w v : ↥(chartAlgFin (N * p) p))) = 0 ∧

    (5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) =
        ∏ a ∈ S, ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p))) ^ (12 / jWidth a)) ∧

    (∀ 𝔭 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)), 𝔭.IsPrime →
      (σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) ∈ 𝔭 ↔
        ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p)) ∈ 𝔭)) ∧

    σ₀ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] v) ≠ 0 ∧

    (RingHom.ker σ₀ ∈ minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)) ∈
        minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) ∧
      RingHom.ker σ₀ ≠ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom))) :=
  OggComp.main N κ hpN ι hι w hw σ₀ h0 v hv

end S_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd (solution)
