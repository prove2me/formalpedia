-- Prove2me | solution 1 for ModularCurve.IgusaScheme.map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1e980685-0fb7-5062-9032-1213b95d6008

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure"
p2m_attr_erase "instance" "instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

namespace IgusaFrobRing

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def algHomOfRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B] (f : A →+* B) :
    A →ₐ[ℤp] B :=
  { f with
    commutes' := fun c => RingHom.congr_fun (ringHom_ext_zp (p := p) (f.comp (algebraMap ℤp A)) (algebraMap ℤp B)) c }

theorem algHomOfRingHom_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B]
    (f : A →+* B) (a : A) : algHomOfRingHom (p := p) f a = f a := rfl

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

section Main

variable (N : ℕ) [NeZero N]
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem one_tmul_natCast_mul {M : Type*} [CommRing M] [Algebra ℤp M] (c : M) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : M) * c) = 0 := by
  rw [show ((p : ℕ) : M) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem isDomain_tensor_chartAlgFin (hpN : ¬ p ∣ N) : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := by
  let K := AlgebraicClosure κ
  haveI : IsDomain (K ⊗[ℤp] ↥(chartAlgFin N p)) :=
    (isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N p hpN K).1

  let j : κ ⊗[ℤp] ↥(chartAlgFin N p) →ₐ[ℤp] K ⊗[ℤp] ↥(chartAlgFin N p) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤp κ K) (AlgHom.id ℤp ↥(chartAlgFin N p))
  have hinj : Function.Injective j := by
    let f : κ →ₗ[κ] K := Algebra.linearMap κ K
    have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr (algebraMap κ K).injective
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hf
    let f' : κ →ₗ[ℤp] K := f.restrictScalars ℤp
    let g' : K →ₗ[ℤp] κ := g.restrictScalars ℤp
    have hgf : g'.comp f' = LinearMap.id := by
      ext x; exact LinearMap.congr_fun hg x
    have hj : ∀ z, j z = f'.rTensor ↥(chartAlgFin N p) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x b => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    intro z₁ z₂ h
    have := congrArg (g'.rTensor ↥(chartAlgFin N p)) (show f'.rTensor _ z₁ = f'.rTensor _ z₂ by rw [← hj, ← hj, h])
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hgf, LinearMap.rTensor_id,
      LinearMap.id_apply, LinearMap.id_apply] at this
  exact Function.Injective.isDomain j.toRingHom hinj

theorem false_of_one_tmul_j_eq_pow
    (K : Type) [Field K] [Algebra κ K] (g₀ : ↥(chartAlgFin N p) →+* LaurentSeries K)
    (hg₀ : g₀ (jChartFin N p) = jqModC K)
    (s : κ ⊗[ℤp] ↥(chartAlgFin N p)) (hs : (1 : κ) ⊗ₜ[ℤp] jChartFin N p = s ^ p) : False := by

  let χ : κ ⊗[ℤp] ↥(chartAlgFin N p) →+* LaurentSeries K :=
    tensorRingHom (p := p) ((algebraMap K (LaurentSeries K)).comp (algebraMap κ K)) g₀
  have hχj : χ ((1 : κ) ⊗ₜ[ℤp] jChartFin N p) = jqModC K := by
    show tensorRingHom (p := p) _ _ _ = _
    rw [tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC K := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    have := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_zero, order_jqModC] at this
    norm_num at this
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

theorem map_ker_mul_map_ker_le
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* L))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (P : Ideal (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) [hP : P.IsPrime] :
    Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 0)) *
      Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ P := by
  have hrad : (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).radical ≤
      P.comap (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hc' : z ^ n = ((p : ℕ) : ↥(chartAlgFin (N * p) p)) * c := by rw [← hc]; exact mul_comm c _
    rw [Ideal.mem_comap]
    refine hP.mem_of_pow_mem n ?_
    rw [← map_pow, hc', Algebra.TensorProduct.includeRight_apply, one_tmul_natCast_mul κ]
    exact Ideal.zero_mem _
  rw [← Ideal.map_mul]
  refine (Ideal.map_mono ?_).trans (Ideal.map_le_iff_le_comap.mpr hrad)
  rw [← Ideal.sInf_minimalPrimes, hmin, sInf_pair]
  exact Ideal.mul_le_inf

theorem case_zero
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    {L : Type*} [CommRing L] (θ₀ : ↥(chartAlgFin (N * p) p) →+* L)
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ₀ (w (ι b)) = θ₀ (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z))
    (hI0 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker θ₀) ≤ RingHom.ker (σ 0).toRingHom)
    (b : ↥(chartAlgFin N p)) :
    σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b) = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := by
  have hu : (1 : κ) ⊗ₜ[ℤp] (w (ι b) - (ι b) ^ p) ∈ RingHom.ker (σ 0).toRingHom :=
    hI0 (Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, map_pow, hfrob b, sub_self]))
  have hu' : σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := by
    rw [← sub_eq_zero, ← map_sub, ← TensorProduct.tmul_sub]
    exact hu
  calc σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b)
      = σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) := by
        rw [h1, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply]
    _ = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := hu'
    _ = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι (((1 : κ) ⊗ₜ[ℤp] b) ^ p)) := by
        rw [map_pow (Algebra.TensorProduct.map (AlgHom.id κ κ) ι), Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.tmul_pow, one_pow]
    _ = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := h0 _

theorem one_tmul_j_eq_pow_of_case_one
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p)) (hιj : ι (jChartFin N p) = jChartFin (N * p) p)
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* L))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) :
    (1 : κ) ⊗ₜ[ℤp] jChartFin N p = (σ 0 ((1 : κ) ⊗ₜ[ℤp] w.symm (jChartFin (N * p) p))) ^ p := by
  have hv : (1 : κ) ⊗ₜ[ℤp] (jChartFin (N * p) p - (w.symm (jChartFin (N * p) p)) ^ p) ∈
      RingHom.ker (σ 0).toRingHom := by
    refine hI1 (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, AlgEquiv.apply_symm_apply, ← hιj, map_sub, map_pow, hfrob, sub_self]
  have h : σ 0 ((1 : κ) ⊗ₜ[ℤp] (jChartFin (N * p) p - (w.symm (jChartFin (N * p) p)) ^ p)) = 0 :=
    RingHom.mem_ker.mp hv
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at h
  have hl : σ 0 ((1 : κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = (1 : κ) ⊗ₜ[ℤp] jChartFin N p := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jChartFin N p), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← hl, h, ← map_pow (σ 0), Algebra.TensorProduct.tmul_pow, one_pow]

theorem case_one_false
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (K : Type) [Field K] [Algebra κ K] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* LaurentSeries K))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hpin : ∀ (c : ↥(chartAlgFin (N * p) p)) (y : LaurentSeries ℤ),
      ((c : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = coeffMap (Int.castRingHom ℚ) y →
      θ 0 c = coeffMap (Int.castRingHom K) y)
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) : False := by

  have hj1 : (((ι (jChartFin N p) : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := by rw [hι]; rfl
  have hj2 : (((jChartFin (N * p) p : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := rfl
  have hιj : ι (jChartFin N p) = jChartFin (N * p) p := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))
  have hs := one_tmul_j_eq_pow_of_case_one N κ ι hιj w θ hθ1 hfrob σ h0 hI1
  refine false_of_one_tmul_j_eq_pow N κ K ((θ 0).comp ι.toRingHom) ?_ _ hs
  show θ 0 (ι (jChartFin N p)) = jqModC K
  rw [hιj, hpin (jChartFin (N * p) p) (jqModC ℤ)]
  · exact coeffMap_jqModC (Int.castRingHom K)
  · show jq = _
    rw [coeffMap_jqModC, jqModC_rat]

theorem main (hpN : ¬ p ∣ N)
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z))
    (b : ↥(chartAlgFin N p)) :
    σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b) = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := isDomain_tensor_chartAlgFin N κ hpN
  haveI : CharP (AlgebraicClosure κ) p :=
    charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p
  obtain ⟨θ, hθ1, hpin, -, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N p hpN ι hι w hw (AlgebraicClosure κ)
  haveI hP : (RingHom.ker (σ 0).toRingHom).IsPrime := RingHom.ker_isPrime _
  rcases hP.mul_le.mp (map_ker_mul_map_ker_le N κ θ hmin (RingHom.ker (σ 0).toRingHom)) with hI0 | hI1
  · exact case_zero N κ ι w (θ 0) hfrob σ h0 h1 hI0 b
  · exact (case_one_false N κ ι hι w σ h0 (AlgebraicClosure κ) θ hθ1 hpin hfrob hI1).elim

end Main

section KerRetr

variable (N : ℕ) [NeZero N]
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem jqModC_sub_pow_ne_zero (K : Type) [Field K] : jqModC K - jqModC K ^ (p * p) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have h0 : jqModC K ≠ 0 := by
    intro h0
    have := order_jqModC K
    rw [h0, HahnSeries.order_zero] at this
    norm_num at this
  have hord : ∀ n : ℕ, (jqModC K ^ n).order = n * (jqModC K).order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n h0) h0, ih]; push_cast; ring
  have := congrArg HahnSeries.order h
  rw [hord, order_jqModC] at this
  have hp : (1 : ℤ) < p * p := by
    have h1 : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    nlinarith
  push_cast at this
  linarith

theorem kerRetr (hpN : ¬ p ∣ N)
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (𝔭 : Ideal ↥(chartAlgFin (N * p) p))
    (h𝔭 : 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes) :
    Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) 𝔭
        ≤ RingHom.ker σ₀.toRingHom ↔
      w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∈ 𝔭 := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := isDomain_tensor_chartAlgFin N κ hpN
  haveI : CharP (AlgebraicClosure κ) p :=
    charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p
  obtain ⟨θ, hθ1, hpin, hne, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N p hpN ι hι w hw (AlgebraicClosure κ)

  let σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)) := fun _ => σ₀
  haveI hP : (RingHom.ker (σ 0).toRingHom).IsPrime := RingHom.ker_isPrime _

  have hj1 : (((ι (jChartFin N p) : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := by rw [hι]; rfl
  have hj2 : (((jChartFin (N * p) p : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := rfl
  have hιj : ι (jChartFin N p) = jChartFin (N * p) p := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))

  have hww : ∀ c, w (w c) = c := by
    obtain ⟨w', hw', hww'⟩ := exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull N p hpN
    have he : ∀ c, w c = w' c := fun c => Subtype.ext (by rw [hw, hw'])
    intro c
    rw [he, he]
    exact AlgEquiv.congr_fun hww' c

  have hu0 : w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∈ RingHom.ker (θ 0) := by
    rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self]
  have hθj : θ 0 (jChartFin (N * p) p) = jqModC (AlgebraicClosure κ) := by
    rw [hpin (jChartFin (N * p) p) (jqModC ℤ)]
    · exact coeffMap_jqModC (Int.castRingHom (AlgebraicClosure κ))
    · show jq = _
      rw [coeffMap_jqModC, jqModC_rat]
  have hu1 : w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∉ RingHom.ker (θ 1) := by
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, hww, map_sub, map_pow, hfrob, hιj, hθj, ← pow_mul]
    exact jqModC_sub_pow_ne_zero (p := p) (AlgebraicClosure κ)

  have hnot1 : ¬ Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp]
      κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom :=
    fun hI1 => case_one_false N κ ι hι w σ h0 (AlgebraicClosure κ) θ hθ1 hpin hfrob hI1

  have hyes0 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp]
      κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) (RingHom.ker (θ 0)) ≤ RingHom.ker (σ 0).toRingHom :=
    (hP.mul_le.mp (map_ker_mul_map_ker_le N κ θ hmin (RingHom.ker (σ 0).toRingHom))).resolve_right hnot1

  have h𝔭' : 𝔭 = RingHom.ker (θ 0) ∨ 𝔭 = RingHom.ker (θ 1) := by
    rw [hmin] at h𝔭
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h𝔭
  rcases h𝔭' with rfl | rfl
  · exact ⟨fun _ => hu0, fun _ => hyes0⟩
  · exact ⟨fun h => (hnot1 h).elim, fun h => (hu1 h).elim⟩

end KerRetr

end IgusaFrobRing

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))

    (σ₀ : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[κ]
        κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)

    (𝔭 : Ideal ↥(chartAlgFin (N * p) p))
    (h𝔭 : 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes) :
    Ideal.map (Algebra.TensorProduct.includeRight :
        ↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) 𝔭 ≤ RingHom.ker σ₀.toRingHom ↔
      w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∈ 𝔭 :=
  IgusaFrobRing.kerRetr N κ hpN ι hι w hw σ₀ h0 𝔭 h𝔭

end
end S_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd (solution)
