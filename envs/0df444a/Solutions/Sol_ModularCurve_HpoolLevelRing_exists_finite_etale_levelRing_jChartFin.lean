-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_jChartFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bed04766-05f1-5817-98e8-b2e1a2f9a88d

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_ringHom_laurentSeries_ker_eq_span_natCast
import Theorems.Thm_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime
import Theorems.Thm_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval_jChartFin
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin
import Theorems.Thm_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing
open scoped TensorProduct

namespace LevelL

variable (p : ℕ) [Fact p.Prime] [NeZero p]

noncomputable abbrev jA : Afin p :=
  AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev Bj (f : ℤ) (g : ℤ[X]) : Type := levelRing p f (jA p) g

theorem isPrime_span_natCast_Afin (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (Ideal.span {((q : ℕ) : Afin p)}).IsPrime := by
  obtain ⟨K, _, _, _, φ, hker, -⟩ := exists_ringHom_laurentSeries_ker_eq_span_natCast p q hq hqp
  rw [← hker]
  exact RingHom.ker_isPrime φ

theorem aeval_jA_notMem_span_natCast (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (g : ℤ[X]) (hg : g.Monic) :
    (Polynomial.aeval (R := ℤ) (jA p) g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)} := by
  obtain ⟨K, _, _, _, φ, hker, hj⟩ := exists_ringHom_laurentSeries_ker_eq_span_natCast p q hq hqp
  rw [← hker, RingHom.mem_ker]
  have h1 : φ (aeval (jA p) g) = aeval (jqModC K) (g.map (Int.castRingHom K)) := by
    rw [← hj, aeval_def, hom_eval₂, aeval_def, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  rw [h1]
  intro h0
  have hne : g.map (Int.castRingHom K) ≠ 0 := (hg.map (Int.castRingHom K)).ne_zero
  exact (ModularCurve.transcendental_jqModC K) ⟨g.map (Int.castRingHom K), hne, h0⟩

theorem irreducible_map_rat_of_irreducible_map_zmod (ℓ : ℕ) [Fact ℓ.Prime] (g : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom (ZMod ℓ)))) : Irreducible (g.map (Int.castRingHom ℚ)) := by
  have hZ : Irreducible g := hg.irreducible_of_irreducible_map (Int.castRingHom (ZMod ℓ)) g hirr
  exact (hg.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hZ

theorem separable_map_zmod_of_irreducible (ℓ : ℕ) [Fact ℓ.Prime] (g : ℤ[X])
    (hirr : Irreducible (g.map (Int.castRingHom (ZMod ℓ)))) : (g.map (Int.castRingHom (ZMod ℓ))).Separable :=
  PerfectField.separable_of_irreducible hirr

omit [Fact (Nat.Prime p)] in

theorem transcendental_int_jFull : Transcendental ℤ (IgusaScheme.jFull p) := by
  rintro ⟨q, hq0, hq⟩
  apply ModularCurve.transcendental_jq
  refine ⟨q.map (Int.castRingHom ℚ), (Polynomial.map_ne_zero_iff (Int.castRingHom ℚ).injective_int).mpr hq0, ?_⟩

  set ψ : ↥(modularFunctionFieldFull p) →+* LaurentSeries ℚ :=
    algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ) with hψ
  have hval : ψ (aeval (IgusaScheme.jFull p) q) = aeval jq (q.map (Int.castRingHom ℚ)) := by
    rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
    have hj : ψ (IgusaScheme.jFull p) = jq := rfl
    rw [hj]
    congr 1
    exact RingHom.ext_int _ _
  rw [← hval, hq, map_zero]

noncomputable scoped instance algebraPolyAfin : Algebra ℤ[X] (Afin p) :=
  (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
    (IgusaScheme.jFull p)).toRingHom.toAlgebra

theorem algebraMap_poly_apply (q : ℤ[X]) :
    algebraMap ℤ[X] (Afin p) q = Polynomial.aeval (R := ℤ) (jA p) q := rfl

scoped instance isScalarTower_int_poly_Afin : IsScalarTower ℤ ℤ[X] (Afin p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℤ[X]) (A := Afin p) (RingHom.ext_int _ _)

scoped instance moduleFinite_poly_Afin : Module.Finite ℤ[X] (Afin p) := by
  haveI := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  exact (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf ℤ ℚ
    ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (transcendental_int_jFull p)
    (ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p) inferInstance).1

noncomputable abbrev Ig (g : ℤ[X]) : Ideal (Afin p) := Ideal.span {(Polynomial.aeval (R := ℤ) (jA p) g : Afin p)}

scoped instance moduleFinite_int_quotient (g : ℤ[X]) [hg : Fact g.Monic] : Module.Finite ℤ (Afin p ⧸ Ig p g) :=
  Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem ℤ (Afin p) g (by rw [hg.out.leadingCoeff]; exact isUnit_one) _
    (by rw [algebraMap_poly_apply]; exact Ideal.mem_span_singleton_self _)

theorem aeval_algebraMap_jA (f : ℤ) (g : ℤ[X]) :
    Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) (jA p)) g =
      algebraMap (Afin p) (AfinAway p f) (Polynomial.aeval (R := ℤ) (jA p) g : Afin p) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1

theorem Ig_le_comap (f : ℤ) (g : ℤ[X]) :
    Ig p g ≤ (Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) (jA p)) g}).comap
      (algebraMap (Afin p) (AfinAway p f)) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← aeval_algebraMap_jA]
  exact Ideal.mem_span_singleton_self _

noncomputable def quotToBj (f : ℤ) (g : ℤ[X]) : (Afin p ⧸ Ig p g) →+* Bj p f g :=
  Ideal.quotientMap _ (algebraMap (Afin p) (AfinAway p f)) (Ig_le_comap p f g)

noncomputable scoped instance algebraQuotLevelRing (f : ℤ) (g : ℤ[X]) : Algebra (Afin p ⧸ Ig p g) (Bj p f g) :=
  (quotToBj p f g).toAlgebra

noncomputable scoped instance moduleQuotLevelRing (f : ℤ) (g : ℤ[X]) : Module (Afin p ⧸ Ig p g) (Bj p f g) :=
  Algebra.toModule

theorem quotToBj_comp_mk (f : ℤ) (g : ℤ[X]) :
    (algebraMap (Afin p ⧸ Ig p g) (Bj p f g)).comp (Ideal.Quotient.mk (Ig p g)) =
      (Ideal.Quotient.mk _).comp (algebraMap (Afin p) (AfinAway p f)) := by
  rw [RingHom.algebraMap_toAlgebra]
  exact Ideal.quotientMap_comp_mk (Ig_le_comap p f g)

theorem algebraMap_quot_mk (f : ℤ) (g : ℤ[X]) (a : Afin p) :
    algebraMap (Afin p ⧸ Ig p g) (Bj p f g) (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap (Afin p) (AfinAway p f) a) := rfl

set_option maxHeartbeats 3200000 in

scoped instance isLocalization_Bj (f : ℤ) (g : ℤ[X]) :
    IsLocalization (Algebra.algebraMapSubmonoid (Afin p ⧸ Ig p g) (Submonoid.powers f)) (Bj p f g) := by
  have h := IsLocalization.of_surjective (Submonoid.powers (algebraMap ℤ (Afin p) f)) (AfinAway p f)
    (Ideal.Quotient.mk (Ig p g)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) (jA p)) g}))
    Ideal.Quotient.mk_surjective (quotToBj_comp_mk p f g).symm (by
      rw [Ideal.mk_ker, Ideal.mk_ker, Ideal.map_span, Set.image_singleton, ← aeval_algebraMap_jA])
  have hM : (Submonoid.powers (algebraMap ℤ (Afin p) f)).map (Ideal.Quotient.mk (Ig p g)) =
      Algebra.algebraMapSubmonoid (Afin p ⧸ Ig p g) (Submonoid.powers f) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers]
    congr 1
  rwa [hM] at h

set_option maxHeartbeats 3200000 in

theorem moduleFinite_Bj (f : ℤ) (g : ℤ[X]) (hg : g.Monic) : Module.Finite (Localization.Away f) (Bj p f g) := by
  haveI : Fact g.Monic := ⟨hg⟩
  have h1 : (algebraMap ℤ (Afin p ⧸ Ig p g)).Finite := RingHom.finite_algebraMap.mpr (moduleFinite_int_quotient p g)
  haveI : IsLocalization.Away (algebraMap ℤ (Afin p ⧸ Ig p g) f) (Bj p f g) := by
    have h := isLocalization_Bj p f g
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h
  have h2 := RingHom.localization_away_map_finite ℤ (Afin p ⧸ Ig p g) (Localization.Away f) (Bj p f g)
    (algebraMap ℤ (Afin p ⧸ Ig p g)) f h1
  have h3 : IsLocalization.Away.map (Localization.Away f) (Bj p f g) (algebraMap ℤ (Afin p ⧸ Ig p g)) f =
      algebraMap (Localization.Away f) (Bj p f g) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext_int _ _)
  rw [h3] at h2
  exact RingHom.finite_algebraMap.mp h2

private theorem _root_.IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing' {R : Type*} [CommRing R]
    [IsPrincipalIdealRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (I.comap (algebraMap R S))).principal
  refine ⟨⟨algebraMap R S x, ?_⟩⟩
  rw [← IsLocalization.map_under M S I]
  change Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) I) = Ideal.span {algebraMap R S x}
  rw [show Ideal.comap (algebraMap R S) I = Ideal.span {x} from hx, Ideal.map_span, Set.image_singleton]

p2m_alias "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin.IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing'" "IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing'"
theorem isDomain_away (f : ℤ) (hf : f ≠ 0) : IsDomain (Localization.Away f) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem noZeroSMulDivisors_Bj (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (g : ℤ[X]) (hg : g.Monic) :
    NoZeroSMulDivisors (Localization.Away f) (Bj p f g) :=
  noZeroSMulDivisors_levelRing_of_forall_isPrime p f hf hpf (jA p) g
    (fun q hq hqp => isPrime_span_natCast_Afin p q hq hqp)
    (fun q hq hqp => aeval_jA_notMem_span_natCast p q hq hqp g hg)

theorem free_Bj (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (g : ℤ[X]) (hg : g.Monic)
    [Module.Finite (Localization.Away f) (Bj p f g)] :
    Module.Free (Localization.Away f) (Bj p f g) := by
  haveI := isDomain_away f hf
  haveI : IsPrincipalIdealRing (Localization.Away f) :=
    IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing' (Submonoid.powers f) (Localization.Away f)
  haveI := noZeroSMulDivisors_Bj p f hf hpf g hg
  exact Module.free_of_finite_type_torsion_free'

theorem charZero_residueField_bot (f : ℤ) (hf : f ≠ 0) (P : Ideal (Localization.Away f)) [P.IsPrime] (hP : P = ⊥) :
    CharZero P.ResidueField := by
  haveI := isDomain_away f hf
  have hinjR : Function.Injective (algebraMap ℤ (Localization.Away f)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have hinj : Function.Injective (algebraMap (Localization.Away f) P.ResidueField) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [Ideal.algebraMap_residueField_eq_zero, hP] at hx
    exact hx
  have h := (hinj.comp hinjR)
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h0 : ((n : ℤ)) = 0 := h (by simp only [Function.comp_apply, map_natCast, map_zero]; exact hn)
  exact_mod_cast h0

theorem etale_and_finrank_fiber_bot (c₀ : ℤ[X])
    (hc₀ : ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀ →
      Algebra.Etale ℚ ((ℚ ⊗[ℤ] Afin p) ⧸ Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (jA p) g}))
    (g : ℤ[X]) (hg : g.Monic) (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (hndvd : ¬ g ∣ c₀)
    (f : ℤ) (hf : f ≠ 0) (P : Ideal (Localization.Away f)) [P.IsPrime] (hP : P = ⊥) :
    Algebra.Etale P.ResidueField (P.Fiber (Bj p f g)) ∧
      Module.finrank P.ResidueField (P.Fiber (Bj p f g)) = (p + 1) * g.natDegree := by
  haveI := charZero_residueField_bot f hf P hP
  obtain ⟨h1, h2⟩ := etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient p f (jA p) g P ℚ
  exact ⟨h1 (hc₀ g hg hirr hndvd), h2.trans (finrank_rat_tensorProduct_quotient_span_aeval_jChartFin p g hg.ne_zero)⟩

theorem charP_residueField_span (f : ℤ) (ℓ : ℕ) [Fact ℓ.Prime] (P : Ideal (Localization.Away f)) [P.IsPrime]
    (hP : P = Ideal.span {algebraMap ℤ (Localization.Away f) ℓ}) : CharP P.ResidueField ℓ := by
  have h0 : ((ℓ : ℕ) : P.ResidueField) = 0 := by
    rw [← map_natCast (algebraMap (Localization.Away f) P.ResidueField), Ideal.algebraMap_residueField_eq_zero, hP,
      ← map_natCast (algebraMap ℤ (Localization.Away f))]
    exact Ideal.mem_span_singleton_self _
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).mpr h0

theorem etale_fiber_span (ℓ : ℕ) [Fact ℓ.Prime] (g : ℤ[X])
    (het : Algebra.Etale (ZMod ℓ) ((ZMod ℓ ⊗[ℤ] Afin p) ⧸
      Ideal.span {(1 : ZMod ℓ) ⊗ₜ[ℤ] Polynomial.aeval (jA p) g}))
    (f : ℤ) (P : Ideal (Localization.Away f)) [P.IsPrime]
    (hP : P = Ideal.span {algebraMap ℤ (Localization.Away f) ℓ}) :
    Algebra.Etale P.ResidueField (P.Fiber (Bj p f g)) := by
  haveI := charP_residueField_span f ℓ P hP
  letI : Algebra (ZMod ℓ) P.ResidueField := ZMod.algebra _ ℓ
  exact (etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient p f (jA p) g P (ZMod ℓ)).1 het

theorem finrank_and_rankAtStalk (f : ℤ) (hf : f ≠ 0) (g : ℤ[X]) [Module.Finite (Localization.Away f) (Bj p f g)]
    [Module.Free (Localization.Away f) (Bj p f g)] (r : ℕ)
    (hrank : ∀ (P : Ideal (Localization.Away f)) [P.IsPrime], P = ⊥ →
      Module.finrank P.ResidueField (P.Fiber (Bj p f g)) = r) :
    Module.finrank (Localization.Away f) (Bj p f g) = r ∧
      ∀ 𝔮 : PrimeSpectrum (Localization.Away f), Module.rankAtStalk (R := Localization.Away f) (Bj p f g) 𝔮 = r := by
  haveI := isDomain_away f hf
  have h1 : Module.finrank (Localization.Away f) (Bj p f g) = r := by
    rw [← hrank ⊥ rfl]
    exact (Module.finrank_baseChange (R := (⊥ : Ideal (Localization.Away f)).ResidueField)
      (S := Localization.Away f) (M' := Bj p f g)).symm
  refine ⟨h1, fun 𝔮 => ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, h1]
  rfl

end LevelL
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin.LevelL"

open LevelL in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    ∃ (avoid : (ZMod ℓ)[X]) (_ : avoid ≠ 0) (c₀ : ℤ[X]) (_ : c₀ ≠ 0),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod ℓ))) →
        IsCoprime (g.map (Int.castRingHom (ZMod ℓ))) avoid → ¬ g ∣ c₀ →
        ∃ c : ℤ, ¬ (ℓ : ℤ) ∣ c ∧ c ≠ 0 ∧ ∀ f : ℤ, f ≠ 0 → c ∣ f →
          Module.Finite (Localization.Away f) (levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) ∧
          Algebra.Etale (Localization.Away f) (levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) ∧
          Module.Free (Localization.Away f) (levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) ∧
          Module.finrank (Localization.Away f) (levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) = (p + 1) * g.natDegree ∧
          ∀ 𝔮 : PrimeSpectrum (Localization.Away f),
            Module.rankAtStalk (R := Localization.Away f) (levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) 𝔮 = (p + 1) * g.natDegree := by
  obtain ⟨avoid, havoid, Hℓ⟩ := exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin p ℓ hℓ
  obtain ⟨c₀, hc₀, Hgen⟩ := exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin p
  refine ⟨avoid, havoid, c₀, hc₀, fun g hmon hdeg hirr hcop hndvd => ?_⟩
  have hirrQ := irreducible_map_rat_of_irreducible_map_zmod ℓ g hmon hirr
  have hsep := separable_map_zmod_of_irreducible ℓ g hirr
  have hpp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  haveI : Module.Finite (Localization.Away (p : ℤ)) (Bj p p g) := moduleFinite_Bj p p g hmon
  haveI : Module.Free (Localization.Away (p : ℤ)) (Bj p p g) := free_Bj p p hpp dvd_rfl g hmon
  haveI : Module.Flat (Localization.Away (p : ℤ)) (Bj p p g) := Module.Flat.of_free
  have hgen : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime], P = ⊥ →
      Algebra.Etale P.ResidueField (P.Fiber (Bj p p g)) :=
    fun P _ hP => (etale_and_finrank_fiber_bot p c₀ Hgen g hmon hirrQ hndvd p hpp P hP).1
  have hℓp : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime],
      P = Ideal.span {algebraMap ℤ (Localization.Away (p : ℤ)) ℓ} → Algebra.Etale P.ResidueField (P.Fiber (Bj p p g)) :=
    fun P _ hP => etale_fiber_span p ℓ g (Hℓ g hmon hsep hcop) p P hP
  obtain ⟨c, hc, hℓc, hpc, het⟩ := exists_forall_etale_levelRing_of_etale_fiber p ℓ hℓ (jA p) g hgen hℓp
  refine ⟨c, hℓc, hc, fun f hf hcf => ?_⟩
  haveI := moduleFinite_Bj p f g hmon
  haveI := free_Bj p f hf (dvd_trans hpc hcf) g hmon
  obtain ⟨hfr, hst⟩ := finrank_and_rankAtStalk p f hf g ((p + 1) * g.natDegree)
    (fun P _ hP => (etale_and_finrank_fiber_bot p c₀ Hgen g hmon hirrQ hndvd f hf P hP).2)
  exact ⟨inferInstance, het f hf hcf, inferInstance, hfr, hst⟩

end S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin (solution)
