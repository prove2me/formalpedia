-- Prove2me | solution 1 for ModularCurve.exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/53ffba82-8f4c-511a-b4fe-dc1265b2e703

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel ModularCurve

namespace E147G1

universe u

theorem eq_of_le_of_height_eq_one {S : Type*} [CommRing S] [IsDomain S] {Q P : Ideal S} [hQ : Q.IsPrime]
    (hP : P.IsPrime) (hQ0 : Q ≠ ⊥) (hle : Q ≤ P) (hh : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hle hne
  haveI := hP
  haveI : P.FiniteHeight := (Ideal.finiteHeight_iff P).mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  rw [hh] at h1
  have hQh : Q.height = 0 := ENat.lt_one_iff_eq_zero.mp h1
  haveI : Q.FiniteHeight := (Ideal.finiteHeight_iff Q).mpr (Or.inr (by rw [hQh]; exact ENat.zero_ne_top))
  have hbot : (⊥ : Ideal S) < Q := bot_lt_iff_ne_bot.mpr hQ0
  haveI : (⊥ : Ideal S).IsPrime := Ideal.isPrime_bot
  have h0 := Ideal.height_strict_mono_of_isPrime_of_isPrime hbot
  rw [hQh] at h0
  simp at h0

open PowerSeries HahnSeries in
theorem ofPowerSeries_coeff_neg {R : Type*} [CommRing R] (u : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (ofPowerSeries ℤ R u).coeff k = 0 := by
  rw [ofPowerSeries_apply]
  refine embDomain_notin_range ?_
  rintro ⟨m, hm⟩
  change (m : ℤ) = k at hm
  omega

open PowerSeries HahnSeries in

theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (u : PowerSeries R) :
    qExpand R N (ofPowerSeries ℤ R u) = ofPowerSeries ℤ R (expand N (NeZero.ne N) u) := by
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  ext k
  by_cases hNk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hNk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · rw [ofPowerSeries_coeff_neg _ hm, ofPowerSeries_coeff_neg _ (mul_neg_of_pos_of_neg hN0 hm)]
    · lift m to ℕ using hm with m
      have hcast : ((N : ℤ) * (m : ℤ)) = ((N * m : ℕ) : ℤ) := by push_cast; ring
      rw [ofPowerSeries_apply_coeff, hcast, ofPowerSeries_apply_coeff, coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hNk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [ofPowerSeries_apply_coeff, coeff_expand_of_not_dvd]
      intro h
      exact hNk (by exact_mod_cast h)

open PowerSeries in
theorem expand_injective {R : Type*} [CommRing R] (N : ℕ) (hN : N ≠ 0) : Function.Injective (expand N hN (R := R)) := by
  intro a b h
  ext m
  rw [← coeff_expand_mul N hN a m, ← coeff_expand_mul N hN b m, h]

theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hNk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hNk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hNk, qExpand_coeff_of_not_dvd N _ hNk, map_zero]

end E147G1

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
    :
    ∃ Θ : 𝔔.ResidueField →+* LaurentSeries (IsLocalRing.ResidueField A),
      Function.Injective Θ ∧
      (∀ a : A, Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a)) =
        algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)) ∧
      Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀)) =
        ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
      ∃ z : 𝔔.ResidueField, Θ z = ModularCurve.jqNModC (IsLocalRing.ResidueField A) M' := by
  classical
  have hqprime : q.Prime := Fact.out

  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _

  obtain ⟨W₀, hW₀, hW₀A, hW₀m, hW₀j, hnu⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma0 M') L K₀ hK₀ A j₀ hj₀
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K₀ A W₀ hW₀ hnu

  obtain ⟨hBW, ⟨𝔓, h𝔓pr, h𝔓h, h𝔓mem, h𝔓ϖ, hloc⟩, -⟩ :=
    le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental A L (↥K₀) j₀ htj₀ hFD₀ hsep₀ W₀ hW₀A hW₀m hW₀j
  haveI := h𝔓pr
  haveI : CharP (IsLocalRing.ResidueField A) q := by
    apply (CharP.charP_iff_prime_eq_zero hqprime).mpr
    have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr hAq
    rwa [map_natCast] at h3
  have hM' : (M' : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q]
    exact hqM'
  have hK₀' : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M' (⊤ : Subgroup (ZMod M')ˣ)) := by
    rw [hK₀]
    show _ = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionFieldC ℚ M' ⊤)
    rw [ModularCurve.xHFunctionFieldC_top]
  haveI hspan : (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ}).IsPrime :=
    ModularCurve.isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero M' L A hM' ϖ hϖ K₀ hK₀' j₀ hj₀
  have hϖ0 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ≠ 0 := by
    intro h0
    have h1 : algebraMap A ↥K₀ ϖ = 0 := by
      have := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) => (b : ↥K₀)) h0
      simpa using this
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, map_eq_zero_iff _ (algebraMap L ↥K₀).injective,
      map_eq_zero_iff _ (IsFractionRing.injective A L)] at h1
    apply IsDiscreteValuationRing.not_a_field A
    rw [hϖ, h1, Ideal.span_singleton_eq_bot]
  have hspan0 : Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖ0
  have hQeq : Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ} = 𝔔 :=
    E147G1.eq_of_le_of_height_eq_one inferInstance hspan0 ((Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔔) h𝔔
  have hPeq : Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ} = 𝔓 :=
    E147G1.eq_of_le_of_height_eq_one h𝔓pr hspan0
      ((Ideal.span_singleton_le_iff_mem _).mpr (h𝔓ϖ ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ))) h𝔓h
  have h𝔓𝔔 : 𝔓 = 𝔔 := hPeq.symm.trans hQeq
  subst h𝔓𝔔

  obtain ⟨V, hVmem, hCV, hcen, -, ιV, hιV⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K₀) 𝔓 h𝔔
  have hVW : V = W₀ := by
    ext f
    rw [hVmem, hloc]
    constructor
    · rintro ⟨a, b, hb, h⟩; exact ⟨a, b, hb, h⟩
    · rintro ⟨a, b, hb, h⟩; exact ⟨a, b, hb, h⟩
  subst hVW

  let redbar : IsLocalRing.ResidueField ↥V →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥V) red (fun a ha => by
      rw [← hker] at ha
      exact ha)
  have hredbar : ∀ w : ↥V, redbar (IsLocalRing.residue ↥V w) = red w := fun w => Ideal.Quotient.lift_mk _ _ _
  let Θ : 𝔓.ResidueField →+* LaurentSeries (IsLocalRing.ResidueField A) := redbar.comp ιV.symm.toRingHom
  have hΘC : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔓.ResidueField c) = red ⟨algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ c, hCV c⟩ := by
    intro c
    show redbar (ιV.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔓.ResidueField c)) = _
    rw [← hιV c (hCV c), RingEquiv.symm_apply_apply, hredbar]

  obtain ⟨⟨x, y, hy, hxy, hval⟩, -⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand q L A hAq
  refine ⟨Θ, Θ.injective, ?_, ?_, ?_⟩
  ·
    intro a
    rw [hΘC]
    have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hpres : (((⟨algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a), hCV _⟩ : ↥V) : ↥K₀) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
      show ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a) : ↥K₀) : LaurentSeries L) = HahnSeries.C (algebraMap A L a)
      rw [← IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀, IsScalarTower.algebraMap_apply A L ↥K₀]
      show algebraMap L (LaurentSeries L) (algebraMap A L a) = HahnSeries.C (algebraMap A L a)
      first
        | (rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C])
        | (simp [HahnSeries.algebraMap_apply])
    rw [hred _ _ _ h1 hpres, map_one, map_one, div_one, PowerSeries.map_C]
    first
      | (rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap])
      | (rw [HahnSeries.ofPowerSeries_C]; simp [HahnSeries.algebraMap_apply])
  ·
    rw [hΘC]
    have hpres : (((⟨algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (jChartFin A (↥K₀) j₀), hCV _⟩ : ↥V) : ↥K₀) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
      show ((jChartFin A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) * _ = _
      rw [coe_jChartFin, hj₀]
      exact hxy
    rw [hred _ _ _ hy hpres]
    exact hval
  ·
    have hmemQ : qExpand ℚ M' jq ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') := by
      have h := ModularCurve.qExpand_jqModC_mem_intFormRatiosC_gammaH ℚ M' M' dvd_rfl (⊤ : Subgroup (ZMod M')ˣ)
      rw [CohCarrier.GammaH_top, jqModC_rat] at h
      exact intFormRatiosC_subset ℚ _ h
    have hmemK : coeffEmb L (qExpand ℚ M' jq) ∈ K₀ := by
      rw [hK₀]; exact coeffEmb_mem_laurentBaseChange L hmemQ
    set fM : ↥K₀ := ⟨coeffEmb L (qExpand ℚ M' jq), hmemK⟩ with hfM
    have hfMcoe : (fM : LaurentSeries L) = qExpand L M' (coeffEmb L jq) := by
      show coeffEmb L (qExpand ℚ M' jq) = _
      rw [coeffEmb, E147G1.coeffMap_qExpand']
    have hM0 : M' ≠ 0 := NeZero.ne M'
    have hy' : (PowerSeries.expand M' hM0 y).map (IsLocalRing.residue A) ≠ 0 := by
      rw [PowerSeries.map_expand]
      intro h0
      exact hy (E147G1.expand_injective M' hM0 (by rw [h0, map_zero]))
    have hpres : (fM : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand M' hM0 y).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand M' hM0 x).map (algebraMap A L)) := by
      rw [hfMcoe, PowerSeries.map_expand, PowerSeries.map_expand, ← E147G1.qExpand_ofPowerSeries,
        ← E147G1.qExpand_ofPowerSeries, ← map_mul, hxy]
    have hfW : fM ∈ V := (hW₀ fM).mpr ⟨_, _, hy', hpres⟩
    have hpres' : (((⟨fM, hfW⟩ : ↥V) : ↥K₀) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand M' hM0 y).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand M' hM0 x).map (algebraMap A L)) := hpres
    have hval' : HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((PowerSeries.expand M' hM0 x).map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((PowerSeries.expand M' hM0 y).map (IsLocalRing.residue A)) =
        jqNModC (IsLocalRing.ResidueField A) M' := by
      rw [PowerSeries.map_expand, PowerSeries.map_expand, ← E147G1.qExpand_ofPowerSeries, ← E147G1.qExpand_ofPowerSeries,
        ← map_div₀, hval]
      rfl
    refine ⟨ιV (IsLocalRing.residue ↥V ⟨fM, hfW⟩), ?_⟩
    show redbar (ιV.symm (ιV _)) = _
    rw [RingEquiv.symm_apply_apply, hredbar, hred _ _ _ hy' hpres']
    exact hval'

end S_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd (solution)
