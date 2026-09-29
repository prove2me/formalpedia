-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/da0884f2-1d64-5277-8642-c606e1541964

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_SwdAlgebra
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_SSHeckeV2_ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun
import Theorems.Thm_ModularCurve_placeWidth_dvd_div_two_iff_dvd_add_div_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero
import Theorems.Thm_ModularCurve_exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq"
p2m_attr_erase "simp" "GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace BIsoExists

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N]

theorem placeWidth_dvd (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K) :
    (placeWidth N x : ℤ) ∣ ((p : ℤ) + 1) / 2 := by
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  obtain ⟨hrat, haff, hss⟩ := hx
  set a₀ := x.evalAt (jGeomGen K N) with ha₀
  set e := placeRamificationJ N x with he
  have hepos : 0 < e := by
    have h := ord_sub_evalAt_pos_of_isRational hrat haff.1
      (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
    rw [he]; unfold placeRamificationJ; omega
  have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
  have hWn : placeWidth N x * e = jWidth a₀ := by
    unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
  by_cases hz : a₀ = 0
  · rw [jWidth_of_eq_zero hz] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 ⟨e, hWn.symm⟩ with hu1 | hu3
    · rw [hu1]; simp
    · have hmem : (0 : K) ∈ ssJSet p K := by rw [← hz, ha₀]; exact hss
      have hp3 := (zero_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu3]; push_cast; omega
  by_cases hs : a₀ = 1728
  · rw [jWidth_of_eq_1728 hs hz] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).1 ⟨e, hWn.symm⟩ with hu1 | hu2
    · rw [hu1]; simp
    · have hmem : (1728 : K) ∈ ssJSet p K := by rw [← hs, ha₀]; exact hss
      have hp4 := (ofNat1728_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu2]; push_cast; omega
  · rw [jWidth_of_ne hz hs] at hWn
    rw [Nat.eq_one_of_mul_eq_one_right hWn]; simp

def indexEquiv (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (k : ℤ) (hk2 : 2 ≤ k) (hk : 2 ∣ k) :
    SSIndex p N K hp5 k ≃ SSIndex p N K hp5 (k + ((p : ℤ) + 1)) where
  toFun x := ⟨x.1, by
    obtain ⟨hss, h2, hdvd, hu, h5⟩ := x.2
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
    refine ⟨hss, by omega, by omega, ?_, h5⟩
    exact (placeWidth_dvd_div_two_iff_dvd_add_div_two_of_mem_ssPlaces p hp5 K N hN x.1 hss k h2 hdvd).1 hu⟩
  invFun y := ⟨y.1, by
    obtain ⟨hss, -, -, hu, h5⟩ := y.2
    refine ⟨hss, hk2, hk, ?_, h5⟩
    exact (placeWidth_dvd_div_two_iff_dvd_add_div_two_of_mem_ssPlaces p hp5 K N hN y.1 hss k hk2 hk).2 hu⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

theorem indexEquiv_fst (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (k : ℤ) (hk2 : 2 ≤ k) (hk : 2 ∣ k) (x : SSIndex p N K hp5 k) :
    (indexEquiv p K N hp5 hN k hk2 hk x).1 = x.1 := rfl

theorem bbar_ne_zero (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (z : Place K ↥(modularFunctionFieldC K N)) (hz : z ∈ ssPlaces p N K) :
    lead N K z ((((p : ℤ) + 1) / 2) * ((jWidth (z.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N z : ℤ)) b ≠ 0 := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  let y : SSIndex p N K hp5 ((p : ℤ) + 1) :=
    ⟨z, hz, by omega, by omega, by simpa using placeWidth_dvd p K N hp5 hN z hz, hp5⟩
  exact SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero p hp5 K N hN b hb y

theorem main (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (k : ℤ) (hk : 1 ≤ k) :
    ∃ e : SSCarrier p N K hp5 k ≃ₗ[K] SSCarrier p N K hp5 (k + ((p : ℤ) + 1)),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ v : SSCarrier p N K hp5 k,
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          ssHeckeFun p N K hp5 (k + ((p : ℤ) + 1)) ℓ (e v) = (ℓ : K) • e (ssHeckeFun p N K hp5 k ℓ v) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  by_cases hadm : 2 ≤ k ∧ 2 ∣ k
  ·
    obtain ⟨hk2, hk2d⟩ := hadm
    have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
    obtain ⟨b, hb, -⟩ := exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero p hp5 N hpN K
    let e := indexEquiv p K N hp5 hN k hk2 hk2d
    let bbar : Place K ↥(modularFunctionFieldC K N) → K := fun z =>
      lead N K z ((((p : ℤ) + 1) / 2) * ((jWidth (z.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N z : ℤ)) b
    have hbbar : ∀ y : SSIndex p N K hp5 (k + ((p : ℤ) + 1)), bbar y.1 ≠ 0 := fun y =>
      bbar_ne_zero p K N hp5 hN b hb y.1 y.2.1
    let E : SSCarrier p N K hp5 k ≃ₗ[K] SSCarrier p N K hp5 (k + ((p : ℤ) + 1)) :=
      { toFun := fun w y => bbar y.1 * w (e.symm y)
        map_add' := fun w w' => by funext y; simp only [Pi.add_apply]; ring
        map_smul' := fun c w => by funext y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
        invFun := fun w x => (bbar (e x).1)⁻¹ * w (e x)
        left_inv := fun w => by
          funext x
          show (bbar (e x).1)⁻¹ * (bbar (e x).1 * w (e.symm (e x))) = w x
          rw [← mul_assoc, inv_mul_cancel₀ (hbbar (e x)), one_mul, Equiv.symm_apply_apply]
        right_inv := fun w => by
          funext y
          show bbar y.1 * ((bbar (e (e.symm y)).1)⁻¹ * w (e (e.symm y))) = w y
          rw [Equiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ (hbbar y), one_mul] }
    refine ⟨E, ?_⟩
    intro ℓ hℓ hℓN hℓp v
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hC := SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun p hp5 K N hN ℓ hℓN hℓp k hk2 e
      (indexEquiv_fst p K N hp5 hN k hk2 hk2d) b hb v
    funext y
    have := congrFun hC y
    simp only at this
    rw [Pi.smul_apply, smul_eq_mul]
    exact this
  ·
    have hem1 : IsEmpty (SSIndex p N K hp5 k) := ⟨fun x => hadm ⟨x.2.2.1, x.2.2.2.1⟩⟩
    have hem2 : IsEmpty (SSIndex p N K hp5 (k + ((p : ℤ) + 1))) := ⟨fun y => by
      obtain ⟨-, h2, hd, -, -⟩ := y.2
      apply hadm
      constructor <;> omega⟩
    let E : SSCarrier p N K hp5 k ≃ₗ[K] SSCarrier p N K hp5 (k + ((p : ℤ) + 1)) :=
      { toFun := fun _ y => hem2.elim y
        map_add' := fun _ _ => funext fun y => hem2.elim y
        map_smul' := fun _ _ => funext fun y => hem2.elim y
        invFun := fun _ x => hem1.elim x
        left_inv := fun w => funext fun x => hem1.elim x
        right_inv := fun w => funext fun y => hem2.elim y }
    exact ⟨E, fun ℓ hℓ _ _ v => funext fun y => hem2.elim y⟩

end BIsoExists

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (k : ℤ) (hk : 1 ≤ k) :
    ∃ e : ModularCurve.SSCarrier p N K hp5 k ≃ₗ[K] ModularCurve.SSCarrier p N K hp5 (k + ((p : ℤ) + 1)),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ v : ModularCurve.SSCarrier p N K hp5 k,
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          ModularCurve.ssHeckeFun p N K hp5 (k + ((p : ℤ) + 1)) ℓ (e v)
            = (ℓ : K) • e (ModularCurve.ssHeckeFun p N K hp5 k ℓ v) :=
  BIsoExists.main p K N hp5 hN k hk

end S_ModularCurve_SSHeckeV2_exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_exists_linearEquiv_ssCarrier_forall_ssHeckeFun_eq_smul (solution)
