-- Prove2me | solution 1 for ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8ada7439-bdc0-5823-88f2-b4124067fd5e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XZeroP_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul_of_embedding
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instIsElliptic_tateBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups
namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC intFormRatiosC_subset qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC XZeroP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul_of_embedding finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq jqModC_mem_intFormRatiosC"
namespace O4Eng
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

open scoped MatrixGroups
open IsLocalRing

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_ofPowerSeries (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_qExpand (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem jqModC_coeff_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : K))
    (x := HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))) (a := 0) (b := -1)
  rw [zero_add] at h
  rw [jqModC, h, one_mul, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

theorem transcendental_of_order_neg {K : Type*} [Field K] (x : LaurentSeries K) (hx : x.order < 0) :
    Transcendental K x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rintro ⟨p, hp0, hpx⟩
  set d := p.natDegree with hd
  have hsm : ∀ (c : K) (y : LaurentSeries K) (n : ℤ),
      (algebraMap K (LaurentSeries K) c * y).coeff n = c * y.coeff n := by
    intro c y n
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  have key : (Polynomial.aeval x p).coeff (d • x.order) = p.leadingCoeff * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single d]
    · rw [hsm, Polynomial.leadingCoeff]
    · intro i hi hid
      have hi' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
      rw [hsm, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow]
      simp only [nsmul_eq_mul]
      have : (i : ℤ) < d := by exact_mod_cast hi'
      nlinarith
    · intro h
      exact absurd (Finset.self_mem_range_succ d) h
  rw [hpx, HahnSeries.coeff_zero] at key
  have h1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h2 : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr) (pow_ne_zero _ hx0)
  exact mul_ne_zero h1 h2 key.symm

theorem order_neg_of_coeff_ne_zero {K : Type*} [Field K] {x : LaurentSeries K} {n : ℤ} (hn : n < 0)
    (h : x.coeff n ≠ 0) : x.order < 0 :=
  lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h) hn

theorem transcendental_jqModC (K : Type*) [Field K] : Transcendental K (jqModC K) :=
  transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := -1) (by norm_num)
    (by rw [jqModC_coeff_neg_one]; exact one_ne_zero))

theorem transcendental_qExpand_jqModC (K : Type*) [Field K] (n : ℕ) [NeZero n] :
    Transcendental K (qExpand K n (jqModC K)) := by
  refine transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := (n : ℤ) * (-1)) ?_ ?_)
  · have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    linarith
  · rw [qExpand_coeff_mul, jqModC_coeff_neg_one]
    exact one_ne_zero

theorem transcendental_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    (z : E) (h : Transcendental K (z : L)) : Transcendental K z :=
  fun hz => h (IntermediateField.isAlgebraic_iff.mp hz)

end Laurent

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨h0, hu⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rw [Subgroup.mem_sup] at hu
  obtain ⟨y, hy, z, hz, hyz⟩ := hu
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, mul_one] at hyz
    exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨h0, hyz ▸ hy⟩)
  · rw [hk.neg_one_zpow, mul_neg_one] at hyz
    right
    have h0' : -γ ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
      simp [h0]
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩
    have : CohCarrier.gamma0Units M ⟨-γ, h0'⟩ = -CohCarrier.gamma0Units M ⟨γ, h0⟩ := by
      ext
      simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map]
    rw [this, ← hyz, neg_neg]
    exact hy

end ModularCurve.O4Eng

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC intFormRatiosC_subset qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC XZeroP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul_of_embedding finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq jqModC_mem_intFormRatiosC"
namespace O4Eng
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

theorem algebraMap_LS_eq_single {R : Type*} [CommRing R] (r : R) :
    algebraMap R (LaurentSeries R) r = HahnSeries.single 0 r := by
  have h1 : algebraMap R (PowerSeries R) r = PowerSeries.C r := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

theorem coeffMap_algebraMap' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (algebraMap R (LaurentSeries R) r) = algebraMap S (LaurentSeries S) (f r) := by
  rw [algebraMap_LS_eq_single, algebraMap_LS_eq_single, coeffMap_single]

theorem coeffMap_aeval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : LaurentSeries R)
    (P : Polynomial R) :
    coeffMap f (Polynomial.aeval t P) = Polynomial.aeval (coeffMap f t) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun r => coeffMap_algebraMap' f r

theorem exists_mul_X_pow_eq_ofPowerSeries {R : Type*} [CommRing R] (g : LaurentSeries R) :
    ∃ (x : PowerSeries R) (d : ℕ), g * HahnSeries.ofPowerSeries ℤ R (PowerSeries.X ^ d) = HahnSeries.ofPowerSeries ℤ R x := by
  by_cases hle : 0 ≤ g.order
  · refine ⟨PowerSeries.X ^ g.order.toNat * g.powerSeriesPart, 0, ?_⟩
    rw [pow_zero, map_one, mul_one, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow,
      ← LaurentSeries.single_order_mul_powerSeriesPart g]
    congr 2
    · simp [Int.toNat_of_nonneg hle]
    · rw [LaurentSeries.single_order_mul_powerSeriesPart]
  · refine ⟨g.powerSeriesPart, (-g.order).toNat, ?_⟩
    rw [HahnSeries.ofPowerSeries_X_pow, LaurentSeries.ofPowerSeries_powerSeriesPart, mul_comm]
    have : 0 ≤ -g.order := by omega
    rw [Int.toNat_of_nonneg this]

end ModularCurve.O4Eng

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC intFormRatiosC_subset qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC XZeroP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul_of_embedding finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq jqModC_mem_intFormRatiosC"
namespace O4Red
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve.O4Eng

theorem mem_nonunits_iff' {F : Type*} [Field F] (O : ValuationSubring F) (f : F) :
    f ∈ O.nonunits ↔ f ∈ O ∧ (f = 0 ∨ f⁻¹ ∉ O) := by
  constructor
  · intro h
    exact ⟨(O.valuation_le_one_iff f).mp (le_of_lt ((O.mem_nonunits_iff).mp h)), (O.mem_nonunits_iff_or).mp h⟩
  · rintro ⟨-, h⟩
    exact (O.mem_nonunits_iff_or).mpr h

theorem mem_nonunits_comap_iff {F F' : Type*} [Field F] [Field F'] (O : ValuationSubring F) (ι : F' →+* F)
    (f : F') : f ∈ (O.comap ι).nonunits ↔ ι f ∈ O.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero_iff ι ι.injective]

theorem mem_minimalPrimes_of_height_eq_one {B : Type*} [CommRing B] [IsDomain B] (𝔓 : Ideal B) (hP : 𝔓.IsPrime)
    (hh : 𝔓.height = 1) (ϖ : B) (hϖ : ϖ ∈ 𝔓) (hϖ0 : ϖ ≠ 0) : 𝔓 ∈ (Ideal.span {ϖ}).minimalPrimes := by
  haveI := hP
  haveI : 𝔓.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hh]; exact ENat.one_lt_top))
  refine Ideal.mem_minimalPrimes_of_height_eq ((Ideal.span_singleton_le_iff_mem _).mpr hϖ) ?_
  rw [hh]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ0)

theorem coe_mem_chartAlgFin_of_mem {A : Type} [CommRing A] {L : Type} [Field L]
    (K' K : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K) [Algebra A ↥K'] [Algebra A ↥K]
    (hcompat : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = ((algebraMap A ↥K' a : ↥K') : LaurentSeries L))
    (j' : ↥K') (j : ↥K) (hjj : ((j : ↥K) : LaurentSeries L) = ((j' : ↥K') : LaurentSeries L))
    (b : ↥K') (hb : b ∈ chartAlgFin A (↥K') j') :
    (IntermediateField.inclusion hle b) ∈ chartAlgFin A (↥K) j := by

  let ι : ↥K' →ₐ[A] ↥K :=
    { (IntermediateField.inclusion hle).toRingHom with
      commutes' := fun a => Subtype.ext (by
        show ((IntermediateField.inclusion hle (algebraMap A ↥K' a) : ↥K) : LaurentSeries L) = _
        rw [hcompat]; rfl) }
  have hιapp : ∀ x : ↥K', ι x = IntermediateField.inclusion hle x := fun x => rfl
  have hιj : ι j' = j := by rw [hιapp]; exact Subtype.ext hjj.symm

  have hmap : ∀ x : ↥(Algebra.adjoin A ({j'} : Set ↥K')), ι (x : ↥K') ∈ Algebra.adjoin A ({j} : Set ↥K) := by
    intro x
    have h1 : ι (x : ↥K') ∈ (Algebra.adjoin A ({j'} : Set ↥K')).map ι := Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩
    rwa [AlgHom.map_adjoin, Set.image_singleton, hιj] at h1
  let φ : ↥(Algebra.adjoin A ({j'} : Set ↥K')) →+* ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    ((ι.comp (Algebra.adjoin A ({j'} : Set ↥K')).val).codRestrict (Algebra.adjoin A ({j} : Set ↥K)) hmap).toRingHom
  show IsIntegral _ ((IntermediateField.inclusion hle).toRingHom (b : ↥K'))
  exact IsIntegral.map_of_comp_eq φ (IntermediateField.inclusion hle).toRingHom (by ext x; rfl) hb

section Gauss

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L]

theorem gauss_mem_of_coeffMap (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (g : LaurentSeries A) (f : ↥K) (hf : (f : LaurentSeries L) = coeffMap (algebraMap A L) g) : f ∈ O := by
  obtain ⟨x, d, hx⟩ := exists_mul_X_pow_eq_ofPowerSeries g
  rw [hO]
  refine ⟨x, PowerSeries.X ^ d, ?_, ?_⟩
  · rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  · rw [← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries, hf, ← map_mul, hx]

theorem gauss_algebraMap_mem (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (a : A) (f : ↥K) (hf : (f : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a)) :
    f ∈ O :=
  gauss_mem_of_coeffMap K O hO (algebraMap A (LaurentSeries A) a) f (by rw [hf, coeffMap_algebraMap'])

theorem gauss_mem_nonunits (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hinj : Function.Injective (algebraMap A L)) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (f : ↥K) (hf : (f : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a)) :
    f ∈ O.nonunits := by
  rw [mem_nonunits_iff']
  refine ⟨gauss_algebraMap_mem K O hO a f hf, ?_⟩
  by_cases ha0 : a = 0
  · left
    apply Subtype.ext
    rw [hf, ha0, map_zero, map_zero]
    rfl
  · right
    intro hinv
    rw [hO] at hinv
    obtain ⟨x, y, hy, hxy⟩ := hinv
    apply hy

    have hfL : ((f⁻¹ : ↥K) : LaurentSeries L) = (algebraMap L (LaurentSeries L) (algebraMap A L a))⁻¹ := by
      rw [← hf]; rfl
    have haL : algebraMap L (LaurentSeries L) (algebraMap A L a) ≠ 0 := by
      rw [algebraMap_LS_eq_single]
      exact HahnSeries.single_ne_zero ((map_ne_zero_iff _ hinj).mpr ha0)
    rw [hfL, inv_mul_eq_iff_eq_mul₀ haL] at hxy
    have hyx : y.map (algebraMap A L) = (PowerSeries.C a * x).map (algebraMap A L) := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      rw [hxy, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, algebraMap_LS_eq_single]
      rfl
    have hyx' : y = PowerSeries.C a * x := by
      ext n
      have := congrArg (PowerSeries.coeff n) hyx
      simp only [PowerSeries.coeff_map] at this
      exact hinj this
    rw [hyx', map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero, zero_mul]

theorem gauss_aeval_mem_and_inv_mem (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra ℚ L] (hinj : Function.Injective (algebraMap A L))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval j P ∈ O ∧ (Polynomial.aeval j P)⁻¹ ∈ O := by
  classical

  set g : LaurentSeries A := Polynomial.aeval (jqModC A) P with hg
  have hjg : (j : LaurentSeries L) = coeffMap (algebraMap A L) (jqModC A) := by
    rw [hj, coeffMap_jqModC]
    show coeffMap (algebraMap ℚ L) jq = jqModC L
    rw [← jqModC_rat, coeffMap_jqModC]
  have hfg : ((Polynomial.aeval j P : ↥K) : LaurentSeries L) = coeffMap (algebraMap A L) g := by
    rw [hg, coeffMap_aeval, ← hjg, ← Polynomial.aeval_map_algebraMap L, ← IntermediateField.coe_val,
      ← Polynomial.aeval_algHom_apply]
  have hmem := gauss_mem_of_coeffMap K O hO g _ hfg
  refine ⟨hmem, ?_⟩

  have hgbar : coeffMap (IsLocalRing.residue A) g ≠ 0 := by
    rw [hg, coeffMap_aeval, coeffMap_jqModC]
    intro h0
    exact transcendental_jqModC (IsLocalRing.ResidueField A) ⟨P.map (IsLocalRing.residue A), hP, h0⟩
  obtain ⟨x, d, hx⟩ := exists_mul_X_pow_eq_ofPowerSeries g
  have hxbar : x.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    apply hgbar
    have h1 := congrArg (coeffMap (IsLocalRing.residue A)) hx
    rw [map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, h0, map_zero, map_pow, PowerSeries.map_X,
      HahnSeries.ofPowerSeries_X_pow] at h1
    exact (mul_eq_zero.mp h1).resolve_right (by simp)
  rw [hO]
  refine ⟨PowerSeries.X ^ d, x, hxbar, ?_⟩
  have hf0 : ((Polynomial.aeval j P : ↥K) : LaurentSeries L) ≠ 0 := by
    rw [hfg]
    intro h0
    apply hgbar
    have : g = 0 := by
      ext k
      have := congrArg (fun s : LaurentSeries L => s.coeff k) h0
      simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
      exact (map_eq_zero_iff _ hinj).mp this
    rw [this, map_zero]
  have hxL := congrArg (coeffMap (algebraMap A L)) hx
  rw [map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, ← hfg] at hxL
  rw [show (((Polynomial.aeval j P)⁻¹ : ↥K) : LaurentSeries L) = (((Polynomial.aeval j P) : ↥K) : LaurentSeries L)⁻¹ from rfl,
    inv_mul_eq_iff_eq_mul₀ hf0]
  exact hxL.symm

end Gauss

end ModularCurve.O4Red

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀ : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion (hle₀.trans hle')).toRingHom.toAlgebra
    letI : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
    ∀ (B : ValuationSubring ↥K),
      (∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀) →
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ B.nonunits → b ∈ y.asIdeal) →
        ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀' := by
  intro B hBO₀ hBy x
  classical
  letI instK₀K : Algebra ↥K₀ ↥K := (IntermediateField.inclusion (hle₀.trans hle')).toRingHom.toAlgebra
  letI instK₀'K : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra

  set ι' : ↥K₀' →ₐ[L] ↥K := IntermediateField.inclusion hle' with hι'
  set ι₀ : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion (hle₀.trans hle') with hι₀
  set ι₀' : ↥K₀ →ₐ[L] ↥K₀' := IntermediateField.inclusion hle₀ with hι₀'
  have hιι : ∀ x : ↥K₀, ι' (ι₀' x) = ι₀ x := fun x => rfl

  letI algAK₀' : Algebra A ↥K₀' := ((algebraMap L ↥K₀').comp (algebraMap A L)).toAlgebra
  haveI istAK₀' : IsScalarTower A L ↥K₀' := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  letI algAK₀ : Algebra A ↥K₀ := ((algebraMap L ↥K₀).comp (algebraMap A L)).toAlgebra
  haveI istAK₀ : IsScalarTower A L ↥K₀ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have halgK : ∀ a : A, algebraMap A ↥K a = ι' (algebraMap A ↥K₀' a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, show algebraMap A ↥K₀' a = algebraMap L ↥K₀' (algebraMap A L a) from rfl,
      AlgHom.commutes]
  have halgK₀ : ∀ a : A, algebraMap A ↥K a = ι₀ (algebraMap A ↥K₀ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, show algebraMap A ↥K₀ a = algebraMap L ↥K₀ (algebraMap A L a) from rfl,
      AlgHom.commutes]

  have hjq : ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') := by
    have := ModularCurve.intFormRatiosC_subset ℚ (CongruenceSubgroup.Gamma0 M') (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
    rwa [ModularCurve.jqModC_rat] at this
  have hj₀mem : (j : LaurentSeries L) ∈ K₀ := by
    rw [hj, hK₀]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L hjq
  set j₀ : ↥K₀ := ⟨(j : LaurentSeries L), hj₀mem⟩ with hj₀def
  set j' : ↥K₀' := ι₀' j₀ with hj'def
  have hj' : ((j' : ↥K₀') : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := hj
  have hj₀ : ((j₀ : ↥K₀) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := hj
  have hιj : ι' j' = j := Subtype.ext rfl
  have hιj₀ : ι₀ j₀ = j := Subtype.ext rfl
  haveI : Fact (j' ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by rw [← hιj, h, map_zero])⟩

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q * M') := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI : (CongruenceSubgroup.Gamma0 (q * M')).FiniteIndex := by
    rw [← CohCarrier.GammaH_top]; exact Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH _ _)
  have htj : Transcendental A j' := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀' A j' hj'
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (q * M')) hT L K₀' hK₀' j' hj'
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K₀')) ↥K₀' :=
    Algebra.IsSeparable.of_integral _ _

  have haeval₀ : ∀ P : Polynomial A, ι₀ (Polynomial.aeval j₀ P) = Polynomial.aeval j P := by
    intro P
    rw [← hιj₀]; exact (Polynomial.aeval_algHom_apply (ι₀.restrictScalars A) j₀ P).symm
  have haeval' : ∀ P : Polynomial A, ι' (Polynomial.aeval j' P) = Polynomial.aeval j P := by
    intro P
    rw [← hιj]; exact (Polynomial.aeval_algHom_apply (ι'.restrictScalars A) j' P).symm

  set B' : ValuationSubring ↥K₀' := B.comap ι'.toRingHom with hB'
  have hB'mem : ∀ f : ↥K₀', f ∈ B' ↔ ι' f ∈ B := fun f => Iff.rfl
  have hW' : ∀ f : ↥K₀', ι' f ∈ W₀ ↔ f ∈ O₀' := fun f => by rw [hW₀, hO₀']; exact Iff.rfl

  have hBA : ∀ a : A, algebraMap A ↥K₀' a ∈ B' := by
    intro a
    rw [hB'mem, ← halgK, halgK₀, show (ι₀ : ↥K₀ →ₐ[L] ↥K) (algebraMap A ↥K₀ a) = algebraMap ↥K₀ ↥K (algebraMap A ↥K₀ a) from rfl,
      hBO₀]
    exact ModularCurve.O4Red.gauss_algebraMap_mem K₀ O₀ hO₀ a _ rfl
  have hBm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₀' a ∈ B'.nonunits := by
    intro a ha
    rw [ModularCurve.O4Red.mem_nonunits_comap_iff]
    show ι' (algebraMap A ↥K₀' a) ∈ B.nonunits
    rw [← halgK, halgK₀]
    have h0 := ModularCurve.O4Red.gauss_mem_nonunits K₀ O₀ hO₀ hinjAL a ha (algebraMap A ↥K₀ a) rfl
    rw [ModularCurve.O4Red.mem_nonunits_iff'] at h0 ⊢
    refine ⟨(hBO₀ _).mpr h0.1, ?_⟩
    rcases h0.2 with h00 | hni
    · left; rw [h00, map_zero]
    · right
      rw [← map_inv₀, show (ι₀ : ↥K₀ →ₐ[L] ↥K) (algebraMap A ↥K₀ a)⁻¹ = algebraMap ↥K₀ ↥K (algebraMap A ↥K₀ a)⁻¹ from rfl, hBO₀]
      exact hni
  have hBj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j' P ∈ B' ∧ (Polynomial.aeval j' P)⁻¹ ∈ B' := by
    intro P hP
    obtain ⟨h1, h2⟩ := ModularCurve.O4Red.gauss_aeval_mem_and_inv_mem K₀ O₀ hO₀ hinjAL j₀ hj₀ P hP
    rw [hB'mem, hB'mem, map_inv₀, haeval', ← haeval₀, ← map_inv₀]
    exact ⟨(hBO₀ _).mpr h1, (hBO₀ _).mpr h2⟩

  have hOA : ∀ a : A, algebraMap A ↥K₀' a ∈ O₀' := fun a => ModularCurve.O4Red.gauss_algebraMap_mem K₀' O₀' hO₀' a _ rfl
  have hOm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₀' a ∈ O₀'.nonunits :=
    fun a ha => ModularCurve.O4Red.gauss_mem_nonunits K₀' O₀' hO₀' hinjAL a ha _ rfl
  have hOj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j' P ∈ O₀' ∧ (Polynomial.aeval j' P)⁻¹ ∈ O₀' :=
    fun P hP => ModularCurve.O4Red.gauss_aeval_mem_and_inv_mem K₀' O₀' hO₀' hinjAL j' hj' P hP

  obtain ⟨-, ⟨𝔓B, hPBpr, hPBht, hPBmem, hPBmax, hPBloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀') j' htj hFD hsep B' hBA hBm hBj
  obtain ⟨-, ⟨𝔓O, hPOpr, hPOht, hPOmem, hPOmax, hPOloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀') j' htj hFD hsep O₀' hOA hOm hOj

  show ι' x ∈ B ↔ x ∈ O₀'
  by_cases heq : 𝔓B = 𝔓O
  · rw [← hB'mem, hPBloc, hPOloc, heq]
  · exfalso

    have hmemK : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j'), (ι' (b : ↥K₀') : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := fun b =>
      ModularCurve.O4Red.coe_mem_chartAlgFin_of_mem K₀' K hle' (fun a => by rw [halgK]; rfl) j' j rfl (b : ↥K₀') b.2
    let incl : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j') →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
      ((ι'.restrictScalars A).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j').val).codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (fun b => hmemK b)
    have hincl : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j'), ((incl b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ι' (b : ↥K₀') :=
      fun b => rfl
    have hinclj : incl (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀') j') = AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j := by
      apply Subtype.ext
      rw [hincl]
      exact hιj

    set y' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j') := Ideal.comap incl.toRingHom y.asIdeal with hy'
    haveI hy'pr : y'.IsPrime := Ideal.comap_isPrime _ _
    have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_isField A
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ, h0, Ideal.span_singleton_eq_bot]
    have hϖW₀ : ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits := by
      refine ModularCurve.O4Red.gauss_mem_nonunits K W₀ hW₀ hinjAL ϖ hϖm _ ?_
      show ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L) = _
      rw [IsScalarTower.algebraMap_apply A L ↥K]
      rfl
    have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := hz₀ _ hϖW₀
    have hyϖ' : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j') ϖ ∈ y' := by
      rw [hy', Ideal.mem_comap]
      show incl (algebraMap A _ ϖ) ∈ y.asIdeal
      rw [AlgHom.commutes]
      exact hϖy

    have hPBle : 𝔓B ≤ y' := by
      intro b hb
      rw [hy', Ideal.mem_comap]
      apply hBy
      show ((incl b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ B.nonunits
      rw [hincl]
      exact (ModularCurve.O4Red.mem_nonunits_comap_iff B ι'.toRingHom (b : ↥K₀')).mp ((hPBmem b).mp hb)
    have hPOle : 𝔓O ≤ y' := by
      intro b hb
      rw [hy', Ideal.mem_comap]
      apply hz₀
      show ((incl b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits
      rw [hincl]
      have h1 := (hPOmem b).mp hb
      rw [ModularCurve.O4Red.mem_nonunits_iff'] at h1 ⊢
      refine ⟨(hW' _).mpr h1.1, ?_⟩
      rcases h1.2 with h0 | hni
      · left; rw [h0, map_zero]
      · right; rw [← map_inv₀, hW']; exact hni

    have hϖ'0 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j') ϖ ≠ 0 := by
      intro h0
      apply hϖ0
      apply hinjAL
      have h1 := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j') => ((b : ↥K₀') : LaurentSeries L)) h0
      simp only [ZeroMemClass.coe_zero, map_zero] at h1
      have h2 : ((algebraMap A ↥K₀' ϖ : ↥K₀') : LaurentSeries L) = 0 := h1
      rw [show algebraMap A ↥K₀' ϖ = algebraMap L ↥K₀' (algebraMap A L ϖ) from rfl] at h2
      have h3 : algebraMap L (LaurentSeries L) (algebraMap A L ϖ) = 0 := h2
      rw [map_eq_zero] at h3
      rw [h3, map_zero]
    have hminB := ModularCurve.O4Red.mem_minimalPrimes_of_height_eq_one 𝔓B hPBpr hPBht _ (hPBmax ϖ hϖm) hϖ'0
    have hminO := ModularCurve.O4Red.mem_minimalPrimes_of_height_eq_one 𝔓O hPOpr hPOht _ (hPOmax ϖ hϖm) hϖ'0

    have hK₂ : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q))) := by
      rw [Nat.mul_comm]; exact hK₀'
    have hφ' : RingHom.ker (φ.comp incl.toRingHom) = y' := by
      rw [← RingHom.comap_ker, hφ]
    have hss := ModularCurve.XZeroP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul_of_embedding
      q M' hqM' L ζ hζ hι K₀' hK₂ A hAq hζA j' hj' ϖ hϖ y' hyϖ' ⟨𝔓B, hminB, 𝔓O, hminO, heq, hPBle, hPOle⟩ Ω
      (φ.comp incl.toRingHom) hφ'
    apply hord
    rw [RingHom.comp_apply] at hss
    have : incl.toRingHom (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀') j') = AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j := hinclj
    rwa [this] at hss

end S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three (solution)
