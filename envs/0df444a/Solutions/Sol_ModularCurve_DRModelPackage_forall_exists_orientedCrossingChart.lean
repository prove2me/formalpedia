-- Prove2me | solution 1 for ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c5c841ab-0627-5da1-8d43-46a8b2dbfa62

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing
import Theorems.Thm_MvPolynomial_CrossingQuotient_ringKrullDim_le
import Theorems.Thm_ModularCurve_DRModelPackage_not_branchIdeal_le_branchIdeal_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackage_residue_baseGerm_surjective_and_isClosed_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackage_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
import Theorems.Thm_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
import Theorems.Thm_ModularCurve_DRModelPackage_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
import Theorems.Thm_ModularCurve_DRModelPackage_exists_span_pair_baseGerm_eq_branchIdeal
import Theorems.Thm_ModularCurve_DRModelPackage_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
import Theorems.Thm_ModularCurve_DRModelPackage_range_compInf_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed
import Theorems.Thm_ModularCurve_DRModel_isIntegral_pullback_toBase
import Theorems.Thm_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.HpoolLevelRing.instCommRingAfin ModularCurve.HpoolLevelRing.instCommRingLevelRing ModularCurve.HpoolLevelRing.instSMulAway ModularCurve.HpoolLevelRing.instModuleAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraAfinAfinAway ModularCurve.HpoolLevelRing.instModuleAway ModularCurve.HpoolLevelRing.instModuleLevelRing ModularCurve.HpoolLevelRing.instCommRingAfinAway ModularCurve.HpoolLevelRing.instModuleAfinSelf ModularCurve.HpoolLevelRing.instSMulAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraLevelRing ModularCurve.HpoolLevelRing.instAlgebraIntAfinAway ModularCurve.HpoolLevelRing.instIsDomainAfin ModularCurve.HpoolLevelRing.instAlgebraIntAfin ModularCurve.HpoolLevelRing.instSMulLevelRing ModularCurve.HpoolLevelRing.algebraAway ModularCurve.HpoolLevelRing.instAlgebraAfinAwayLevelRing ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart.AlgebraicGeometry ModularCurve ModularCurve.DRModelPackage MvPolynomial"

noncomputable section

section Glue

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Scheme.Hom.comp_base Flat Scheme.Hom.comp_apply Scheme.branchIdeal Scheme.mem_branchIdeal_iff Scheme.exists_crossingChart_of_crossingPresentation_stalk" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom Γ Hom.comp_base basicOpen Opens residue Hom.comp_apply branchIdeal mem_branchIdeal_iff exists_crossingChart_of_crossingPresentation_stalk" end AlgebraicGeometry.Scheme
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem AlgebraicGeometry.Scheme.not_mem_basicOpen_of_germ_mem_branchIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x)
    (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)) (hs : X.presheaf.germ U x hxU s ∈ Scheme.branchIdeal h)
    (y : X) (hy : y ∈ closure ({ξ} : Set X)) : y ∉ X.basicOpen s := by
  intro hy'
  have hξU : ξ ∈ U := h.mem_open U.isOpen hxU
  have hgerm : X.presheaf.germ U ξ hξU s ∈ IsLocalRing.maximalIdeal _ := by
    rw [Scheme.branchIdeal, Ideal.mem_comap, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at hs
    exact hs
  have hξ : ξ ∉ X.basicOpen s := fun hh =>
    (IsLocalRing.mem_maximalIdeal _ |>.mp hgerm) ((X.mem_basicOpen s ξ hξU).mp hh)
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy (X.basicOpen s) (X.basicOpen s).isOpen hy'
  rw [Set.mem_singleton_iff] at hz2
  subst hz2
  exact hξ hz1

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem AlgebraicGeometry.Scheme.range_subset_closure_image_genericPoint {C X : Scheme.{u}} [IsIntegral C] (i : C ⟶ X) :
    Set.range i.base ⊆ closure {i.base (genericPoint C)} := by
  rintro _ ⟨c, rfl⟩
  have hc : c ∈ closure ({genericPoint C} : Set C) := by
    rw [genericPoint_closure]; trivial
  have := image_closure_subset_closure_image i.continuous ⟨c, hc, rfl⟩
  simpa [Set.image_singleton] using this

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem AlgebraicGeometry.Scheme.toBase_eq_closedPoint_of_mem_asIdeal {O : Type u} [CommRing O] [IsLocalRing O] (s : O)
    (hs : s ∈ IsLocalRing.maximalIdeal O)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens)
    (f : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme s)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s))) = U.ι ≫ πX)
    (y : ↥(U : Scheme.{u}))
    (hy : CrossingQuotient.U s ∈ (f.base y).asIdeal ∨ CrossingQuotient.V s ∈ (f.base y).asIdeal)
    (hgen : IsLocalRing.maximalIdeal O = Ideal.span {s} ∨ ∃ (q : O) (e : ℕ), 1 ≤ e ∧ s = q ^ e ∧ IsLocalRing.maximalIdeal O = Ideal.span {q}) :
    πX.base (U.ι.base y) = IsLocalRing.closedPoint O := by

  have hsP : algebraMap O (CrossingQuotient O s) s ∈ (f.base y).asIdeal := by
    rw [← CrossingQuotient.U_mul_V]
    rcases hy with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  have h1 : πX.base (U.ι.base y) =
      (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s)))).base (f.base y) := by
    rw [← Scheme.Hom.comp_apply, ← hf, Scheme.Hom.comp_apply]
  rw [h1]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal = IsLocalRing.maximalIdeal O
  have hprime : (Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal).IsPrime := Ideal.comap_isPrime _ _
  symm
  refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le hprime.ne_top ?_
  have hsO : s ∈ Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal := hsP
  rcases hgen with hm | ⟨q, e, he, rfl, hm⟩
  · rw [hm, Ideal.span_singleton_le_iff_mem]; exact hsO
  · rw [hm, Ideal.span_singleton_le_iff_mem]
    exact hprime.mem_of_pow_mem e hsO

end Glue

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

    (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
          (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base x) :
    ∀ n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
        (_ : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base →
            CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base →
            CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) := by
  intro n

  have hbc : bc = DRModel.baseChangeMap toκ := by
    apply pullback.hom_ext
    · rw [hbc₁, DRModel.baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]
    · rw [hbc₂, DRModel.baseChangeMap, pullback.map, pullback.lift_snd]
  subst hbc

  obtain ⟨hinf, hzero⟩ : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n ∧ 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n :=
    letI := (𝔛.ratModel κ).isIntegral
    ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing p 𝔛 O κ toκ n
  haveI : IsIntegral (baseChangeO p O) := ModularCurve.DRModel.isIntegral_pullback_toBase p O hϖ
  have hpO : Irreducible ((p : ℕ) : O) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ

  have hPQ := ModularCurve.DRModelPackage.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal p hp 𝔛 O hϖ κ toκ n hinf hzero
  obtain ⟨hQP, hPQ'⟩ := ModularCurve.DRModelPackage.not_branchIdeal_le_branchIdeal_crossingPt p hp 𝔛 O hϖ κ toκ n hinf hzero
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ModularCurve.DRModelPackage.exists_span_pair_baseGerm_eq_branchIdeal p hp 𝔛 O hϖ κ toκ n hinf hzero
  have hIU := ModularCurve.DRModelPackage.branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm p hp 𝔛 O hϖ κ toκ n hinf hzero
  obtain ⟨t, t', htt', ht, htunit⟩ := ModularCurve.DRModelPackage.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing p hp 𝔛 O hϖ κ toκ n hinf hzero
  obtain ⟨hϖnz, hstalk2⟩ :=
    ModularCurve.DRModelPackage.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk p hp 𝔛 O hϖ κ toκ n hinf hzero
  obtain ⟨hres, hxcl⟩ :=
    ModularCurve.DRModelPackage.residue_baseGerm_surjective_and_isClosed_crossingPt p hp 𝔛 O hϖ κ toκ n hinf hzero (hrat n)
  have hab : a * b ∈ Ideal.span {baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O)} := by
    rw [← hIU]
    refine ⟨?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (ha ▸ Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (hb ▸ Ideal.subset_span (by simp))

  obtain ⟨e, g₀, gi, he1, -, hrel, hg₀, hgi⟩ :
      ∃ (e : ℕ) (g₀ gi : (baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)), 1 ≤ e ∧ e ≤ 12 ∧
        g₀ * gi = baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O) ^ e ∧
        Ideal.span {g₀, baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O)} = Scheme.branchIdeal hzero ∧
        Ideal.span {gi, baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O)} = Scheme.branchIdeal hinf := by
    rcases htunit with hu | hu
    ·
      have htQ : t ∉ Scheme.branchIdeal hinf := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hinf t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hPQ' (by rwa [sup_comm]) hb ha
          (by rwa [mul_comm]) htQ ht htt'
      exact ⟨e, u, v, he1, he, huv, hu', hv'⟩
    ·
      have htQ : t ∉ Scheme.branchIdeal hzero := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hzero t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hQP hPQ ha hb hab htQ ht htt'
      exact ⟨e, v, u, he1, he, by rw [mul_comm]; exact huv, hv', hu'⟩

  obtain ⟨hdom, hic⟩ := MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed (W := O) (((p : ℕ) : O) ^ e)
      (pow_ne_zero e hpO.ne_zero)
  haveI := hdom; haveI := hic
  haveI : LocallyOfFiniteType (baseChangeO.toBase p O) := by
    haveI := 𝔛.isProper
    infer_instance
  haveI : IsLocallyNoetherian (baseChangeO p O) := LocallyOfFiniteType.isLocallyNoetherian (baseChangeO.toBase p O)
  have hmax : IsLocalRing.maximalIdeal ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) =
      Ideal.span {baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O), g₀, gi} := by
    rw [← hPQ, ← hgi, ← hg₀, ← Ideal.span_union]
    congr 1
    ext z
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hdim : ringKrullDim (CrossingQuotient O (((p : ℕ) : O) ^ e)) ≤
      ringKrullDim ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) := by
    refine (MvPolynomial.CrossingQuotient.ringKrullDim_le O 1 ?_ _ (pow_ne_zero e hpO.ne_zero)).trans ?_
    · rw [IsDiscreteValuationRing.ringKrullDim_eq_one O, Nat.cast_one]
    · refine le_trans ?_ hstalk2
      norm_num
  obtain ⟨U, hxU, gU, hU, f, hgerm_g, hgerm_h, -, hover, hfib, hflat, hdictU, hdictV⟩ :=
    AlgebraicGeometry.Scheme.exists_crossingChart_of_crossingPresentation_stalk ((p : ℕ) : O) e
      (baseChangeO.toBase p O) (𝔛.crossingPt O κ toκ n) hxcl g₀ gi hrel hmax hres hdim

  haveI := (𝔛.ratModel κ).isIntegral
  have hvan_g : ∀ y : ↥(baseChangeO p O), 𝔛.ξzero O κ toκ ⤳ y → y ∉ (baseChangeO p O).basicOpen gU := by
    intro y hy
    refine Scheme.not_mem_basicOpen_of_germ_mem_branchIdeal hzero U hxU gU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_g, ← hg₀]; exact Ideal.subset_span (by simp)
  have hvan_h : ∀ y : ↥(baseChangeO p O), 𝔛.ξinf O κ toκ ⤳ y → y ∉ (baseChangeO p O).basicOpen hU := by
    intro y hy
    refine Scheme.not_mem_basicOpen_of_germ_mem_branchIdeal hinf U hxU hU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_h, ← hgi]; exact Ideal.subset_span (by simp)
  have hrange_inf : ∀ y : ↥(baseChangeO p O), y ∈ Set.range (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base →
      𝔛.ξinf O κ toκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (Scheme.range_subset_closure_image_genericPoint (C := (𝔛.ratModel κ).C) (i := 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ) hy)
  have hrange_zero : ∀ y : ↥(baseChangeO p O), y ∈ Set.range (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base →
      𝔛.ξzero O κ toκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (Scheme.range_subset_closure_image_genericPoint (C := (𝔛.ratModel κ).C) (i := 𝔛.compZero κ ≫ DRModel.baseChangeMap toκ) hy)

  have hcover : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∨ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) →
      𝔛.ξinf O κ toκ ⤳ U.ι.base y ∨ 𝔛.ξzero O κ toκ ⤳ U.ι.base y := by
    intro y hy
    have hbase : (baseChangeO.toBase p O).base (U.ι.base y) = IsLocalRing.closedPoint O := by
      refine Scheme.toBase_eq_closedPoint_of_mem_asIdeal (((p : ℕ) : O) ^ e) ?_ (baseChangeO.toBase p O) U f hover y hy
        (Or.inr ⟨(p : O), e, he1, rfl, hϖ⟩)
      rw [hϖ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) e he1
    refine ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_or p 𝔛 O hϖ κ toκ (U.ι.base y) ?_
    intro hmem
    have hmem' : (baseChangeO.toBase p O).base (U.ι.base y) ∈
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := hmem
    rw [hbase] at hmem'
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem' ?_
    change ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
    rw [hϖ]; exact Ideal.mem_span_singleton_self _
  refine ⟨e, he1, U, hxU, f, hover, hfib, hflat, ?_, ?_, ?_, ?_⟩
  ·
    intro y hV

    have hhU : U.ι.base y ∉ (baseChangeO p O).basicOpen hU := (hdictV y).mp hV
    rcases hcover y (Or.inr hV) with h | h
    · rw [(ModularCurve.DRModelPackage.range_compInf_comp_baseChangeMap_eq_closure_and_isClosed p 𝔛 O hϖ κ toκ).1]
      exact specializes_iff_mem_closure.mp h
    · have hUy : CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictU y).mpr (hvan_g _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt O κ toκ n := (hfib y).mp ⟨hUy, hV⟩
      rw [hyx]
      exact ⟨(pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n, by simp [crossingPt, Scheme.Hom.comp_base]⟩
  · intro y hUm
    rcases hcover y (Or.inl hUm) with h | h
    · have hVy : CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictV y).mpr (hvan_h _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt O κ toκ n := (hfib y).mp ⟨hUm, hVy⟩
      rw [hyx]
      refine ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, ?_⟩
      change ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base n =
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n
      rw [← pullback.condition, Category.assoc]
    · rw [(ModularCurve.DRModelPackage.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed p 𝔛 O hϖ κ toκ).1]
      exact specializes_iff_mem_closure.mp h
  · intro y hy
    exact (hdictV y).mpr (hvan_h _ (hrange_inf _ hy))
  · intro y hy
    exact (hdictU y).mpr (hvan_g _ (hrange_zero _ hy))

end

end S_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart (solution)
