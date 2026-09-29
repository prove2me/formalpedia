-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f961c3ee-b3b8-55b4-8af8-a404f81e0064

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_SSHeckeV2_liftFun_spec
import Theorems.Thm_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_ne_zero
import Theorems.Thm_ModularCurve_neg_mul_poleOrder_add_one_le_ord_heckeBetaC_mul_pow
import Theorems.Thm_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
import Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV"
p2m_attr_erase "simp" "LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve~ord_unif WithZero"

namespace FltWs24
namespace RowF

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem neg_le_ord_of_mem_riemannRochSpace {D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0)
    (v : Place K F) : -(D v) ≤ v.ord f := by
  have h := hf v
  unfold Place.ord
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have : WithZero.log (v.adicValuation f) ≤ D v := by
    rwa [WithZero.log_le_iff_le_exp hne]
  omega

theorem min_ord_le_ord_add (v : Place K F) {f g : F} (hfg : f + g ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  unfold Place.ord
  have hmax := Valuation.map_add (v.adicValuation) f g
  have hne : v.adicValuation (f + g) ≠ 0 := v.adicValuation_ne_zero hfg
  rcases le_max_iff.mp hmax with h | h
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation f) :=
      (WithZero.log_le_log hne (v.adicValuation_ne_zero (by assumption))).mpr h
    omega
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation g) :=
      (WithZero.log_le_log hne (v.adicValuation_ne_zero (by assumption))).mpr h
    omega

end FltWs24.RowF

namespace FltWs24
namespace RowF2

p2m_open "AlgebraicCurve ModularCurve~ord_unif"

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

include hp in
theorem isCurveOver_roof (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) : IsCurveOver K ↥(charLDegeneracyRoof K N ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h
    have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h
    push_cast at this
    exact mul_ne_zero hN hℓK this
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNl]
  exact isCurveOver_modularFunctionFieldFullC K (N * ℓ)

include hp in
theorem evalAt_zpow_mul_trace_eq_zero (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0)
    (x : Place K ↥(modularFunctionFieldC K N)) (π : ↥(modularFunctionFieldC K N)) (a : ℤ)
    (Θ : ↥(charLDegeneracyRoof K N ℓ))
    (hΘ : ∀ Y : Place K ↥(charLDegeneracyRoof K N ℓ),
      Y.restrictAlong (heckeAlphaC K N ℓ) (heckeAlphaCIntegral_unconditional K N ℓ) = x →
        1 ≤ Y.ord (heckeAlphaC K N ℓ (π ^ a) * Θ)) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    x.evalAt (π ^ a * Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) Θ) = 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  haveI := isCurveOver_roof p K N ℓ hN hℓK
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h
    have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h
    push_cast at this
    exact mul_ne_zero hN hℓK this
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  have hφ : (heckeAlphaC K N ℓ).toRingHom.IsIntegral := heckeAlphaCIntegral_unconditional K N ℓ
  have hfin : FiniteAlong K (heckeAlphaC K N ℓ) := finiteAlong_heckeAlphaC K N ℓ
  have hsep : SeparableAlong K (heckeAlphaC K N ℓ) := (separableAlong_heckeAlphaC_heckeBetaC K (ℓ := p) N ℓ hpNl).1
  have htr : π ^ a * Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) Θ
      = Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeAlphaC K N ℓ (π ^ a) * Θ) := by
    rw [← smul_eq_mul, ← LinearMap.map_smul_of_tower, Algebra.smul_def]
    rfl
  rw [htr]
  set S := Place.fiberAlong (heckeAlphaC K N ℓ) hφ x with hS
  have hSmem : ∀ Y : Place K ↥(charLDegeneracyRoof K N ℓ), Y ∈ S ↔ Y.restrictAlong (heckeAlphaC K N ℓ) hφ = x := fun Y => Place.mem_fiberAlong
  have hint : ∀ Y ∈ S, heckeAlphaC K N ℓ (π ^ a) * Θ ∈ Y.toValuationSubring := by
    intro Y hY
    have h1 := hΘ Y ((hSmem Y).1 hY)
    have h0 : heckeAlphaC K N ℓ (π ^ a) * Θ ≠ 0 := by intro h; rw [h, Place.ord_zero] at h1; omega
    exact (Y.mem_iff_ord_nonneg h0).2 (by omega)
  obtain ⟨-, hev⟩ := Place.mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt (heckeAlphaC K N ℓ) hφ hfin hsep x S hSmem _ hint
  rw [hev]
  refine Finset.sum_eq_zero fun Y hY => ?_
  have h1 := hΘ Y ((hSmem Y).1 hY)
  have h0 : heckeAlphaC K N ℓ (π ^ a) * Θ ≠ 0 := by intro h; rw [h, Place.ord_zero] at h1; omega
  have hrat : Y.IsRational := (Place.isRational_iff_deg_eq_one Y).2 (IsCurveOver.deg_eq_one_of_isAlgClosed Y)
  rw [(Y.evalAt_eq_zero_iff_one_le_ord hrat h0 (hint Y hY)).2 h1, smul_zero]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem jlit : (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) = jGeomGen K N := rfl

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

private theorem _root_.FltWs24.RowF2.exists_divisor (m : ℕ) : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w := by
  classical
  have hPD := (isCurveOver_modularFunctionFieldC_of_perfectField K N).toHasPrincipalDivisors
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen K N) (jGeomGen_ne_zero K N)
  obtain ⟨D1, hD1, -⟩ := hPD.exists_divisor (jGeomGen K N - algebraMap K _ 1728)
    (jGeomGen_sub_algebraMap_ne_zero K N 1728)
  refine ⟨Finsupp.onFinset (Dj.support ∪ D1.support) (weightFloor K N m) ?_, fun w => by
    rw [Finsupp.onFinset_apply]⟩
  intro w hw
  by_contra hnot
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff, hDj, hD1] at hnot
  apply hw
  unfold weightFloor
  rw [jlit, hnot.1, hnot.2]
  simp

p2m_export "FltWs24.RowF2" "exists_divisor"
include hp in
theorem weightDivisor_ss_m (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (m : ℕ) (z : Place K ↥(modularFunctionFieldC K N))
    (hz : z ∈ ssPlaces p N K) :
    (weightDivisor K N m) z
      = (m : ℤ) * ((jWidth (z.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N z : ℤ) := by
  rw [weightDivisor_apply K N _ (exists_divisor K N _)]
  exact weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K _ z hz.2.1

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem ord_unif (x : Place K ↥(modularFunctionFieldC K N)) : x.ord (unif N K x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact Classical.epsilon_spec (p := fun π : ↥(modularFunctionFieldC K N) => x.ord π = 1)
    ⟨(π : ↥(modularFunctionFieldC K N)), x.ord_coe_irreducible hπ⟩

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem unif_ne_zero (x : Place K ↥(modularFunctionFieldC K N)) : unif N K x ≠ 0 := by
  intro h; have := ord_unif K N x; rw [h, Place.ord_zero] at this; exact zero_ne_one this

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in

theorem zpow_mul_mem_of_le (x : Place K ↥(modularFunctionFieldC K N)) (a : ℤ) {f : ↥(modularFunctionFieldC K N)}
    (hf : f = 0 ∨ -a ≤ x.ord f) : unif N K x ^ a * f ∈ x.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  have hπ := unif_ne_zero K N x
  refine (Place.mem_iff_ord_nonneg x (mul_ne_zero (zpow_ne_zero a hπ) hf0)).mpr ?_
  rw [x.ord_mul (zpow_ne_zero a hπ) hf0, Place.ord_zpow, ord_unif K N x, mul_one]
  rcases hf with h | h
  · exact absurd h hf0
  · omega

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem ord_neg' {F : Type*} [Field F] [Algebra K F] (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord; rw [Valuation.map_neg]

theorem evalAt_add' {F : Type*} [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg' {F : Type*} [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (-f) = -v.evalAt f := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

end FltWs24.RowF2

p2m_open "ModularCurve~ord_unif" in open AlgebraicCurve FltWs24.RowF FltWs24.RowF2 in
theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (m : ℕ) (hm : 1 ≤ m)
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
          haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
          KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
            = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)))
    (G : ↥(modularFunctionFieldC K N))
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
    ∀ (hTG : algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
            Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
              (heckeBetaC K N ℓ G * h ^ m)
              ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m))
      (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))),
      ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x)
          (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
            Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
              (heckeBetaC K N ℓ G * h ^ m))
        = ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ
            (fun y => ModularCurve.lead N K y.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) y) G) x := by
  intro hTG x
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp
      ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
  have hpN : ¬ p ∣ N := fun hd => hN ((CharP.cast_eq_zero_iff K p N).2 hd)
  have hαu : (heckeAlphaC K N ℓ).toRingHom.IsIntegral := heckeAlphaCIntegral_unconditional K N ℓ
  have hβu : (heckeBetaC K N ℓ).toRingHom.IsIntegral := heckeBetaCIntegral_unconditional K N ℓ
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  haveI := isCurveOver_roof p K N ℓ hN hℓK
  have hpNl : ¬ p ∣ N * ℓ := by
    intro hd
    have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 hd
    push_cast at this
    exact mul_ne_zero hN hℓK this
  have hfin : FiniteAlong K (heckeAlphaC K N ℓ) := finiteAlong_heckeAlphaC K N ℓ
  have hsep : SeparableAlong K (heckeAlphaC K N ℓ) := (separableAlong_heckeAlphaC_heckeBetaC K (ℓ := p) N ℓ hpNl).1

  have hhm : h = heckeMultiplier N K ℓ :=
    ModularCurve.SSHeckeV2.eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map p K N hN ℓ hℓN hℓp h hD
  have hh0 : h ≠ 0 := by rw [hhm]; exact ModularCurve.SSHeckeV2.heckeMultiplier_ne_zero p K N hN ℓ hℓN hℓp

  set a : ℤ := poleOrder p N K hp5 (2 * (m : ℤ)) x with ha
  set π := unif N K x.1 with hπdef
  set v : SSCarrier p N K hp5 (2 * (m : ℤ)) := fun y => lead N K y.1 (poleOrder p N K hp5 (2 * (m : ℤ)) y) G with hv
  set G' := liftFun p N K hp5 (2 * (m : ℤ)) v with hG'
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)

  have h2m : (2 * (m : ℤ)) / 2 - 1 = (m : ℤ) - 1 := by omega
  have h2m' : ((2 * (m : ℤ)) / 2).toNat = m := by
    rw [show (2 * (m : ℤ)) / 2 = (m : ℤ) by omega]; exact Int.toNat_natCast m

  have hDx : ∀ y : SSIndex p N K hp5 (2 * (m : ℤ)), (weightDivisor K N m) y.1 = poleOrder p N K hp5 (2 * (m : ℤ)) y := by
    intro y
    rw [weightDivisor_ss_m p K N hp5 hpN m y.1 y.2.1]
    unfold poleOrder
    simp only [Int.mul_ediv_cancel_left _ (two_ne_zero : (2 : ℤ) ≠ 0)]

  obtain ⟨hG'F, hG'L⟩ := ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) v
  rw [h2m'] at hG'F

  set d := G - G' with hd

  have hRHS : ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v x
      = (ℓ : K) ^ (m - 1) * lead N K x.1 a
          (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) ((heckeBetaC K N ℓ) G' * heckeMultiplier N K ℓ ^ m)) := by
    show algebraMap K K ((ℓ : K) ^ ((2 * (m : ℤ)) / 2 - 1)) * lead N K x.1 (poleOrder p N K hp5 (2 * (m : ℤ)) x)
        (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) ((heckeBetaC K N ℓ) (liftFun p N K hp5 (2 * (m : ℤ)) v) * heckeMultiplier N K ℓ ^ ((2 * (m : ℤ)) / 2).toNat)) = _
    rw [h2m, h2m', Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    rw [← zpow_natCast, Nat.cast_sub hm, Nat.cast_one]
  rw [hRHS, ← hhm]

  set TG := Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) ((heckeBetaC K N ℓ) G * h ^ m) with hTGdef
  set TG' := Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) ((heckeBetaC K N ℓ) G' * h ^ m) with hTG'def
  set Td := Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) ((heckeBetaC K N ℓ) d * h ^ m) with hTddef
  have hsplit : TG = TG' + Td := by
    rw [hTGdef, hTG'def, hTddef, ← map_add, hd, map_sub, sub_mul]
    congr 1; ring

  have hrat := isRational K N x.1
  have hconst_ord : ∀ c : K, c ≠ 0 → x.1.ord (algebraMap K ↥(modularFunctionFieldC K N) c) = 0 := by
    intro c hc
    have h1 : 0 ≤ x.1.ord (algebraMap K ↥(modularFunctionFieldC K N) c) :=
      (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr hc)).mp (x.1.algebraMap_mem' c)
    have h2 : 0 ≤ x.1.ord (algebraMap K ↥(modularFunctionFieldC K N) c)⁻¹ := by
      rw [← map_inv₀]
      exact (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr (inv_ne_zero hc))).mp (x.1.algebraMap_mem' c⁻¹)
    rw [Place.ord_inv] at h2
    omega
  have hℓm : ((ℓ : K) ^ (m - 1)) ≠ 0 := pow_ne_zero _ hℓK
  have hTG_ord : TG = 0 ∨ -a ≤ x.1.ord TG := by
    rcases eq_or_ne TG 0 with h0 | h0
    · exact Or.inl h0
    right
    have hne : algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) * TG ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hℓm) h0
    have h1 := neg_le_ord_of_mem_riemannRochSpace hTG hne x.1
    rw [x.1.ord_mul ((map_ne_zero _).mpr hℓm) h0, hconst_ord _ hℓm, zero_add, hDx x] at h1
    exact h1
  have hTG_mem : π ^ a * TG ∈ x.1.toValuationSubring := zpow_mul_mem_of_le K N x.1 a hTG_ord

  have hTd : x.1.evalAt (π ^ a * Td) = 0 ∧ π ^ a * Td ∈ x.1.toValuationSubring := by
    rcases eq_or_ne d 0 with hd0 | hd0
    · have : Td = 0 := by rw [hTddef, hd0, map_zero, zero_mul, map_zero]
      rw [this, mul_zero]
      refine ⟨?_, zero_mem _⟩
      rw [show (0 : ↥(modularFunctionFieldC K N)) = algebraMap K ↥(modularFunctionFieldC K N) 0 from (map_zero _).symm,
        Place.evalAt_algebraMap]

    have hF : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → -(weightDivisor K N m z) ≤ z.ord d := by
      intro z hz
      rcases eq_or_ne G 0 with hG0 | hG0
      ·
        have : d = -G' := by rw [hd, hG0, zero_sub]
        rcases eq_or_ne G' 0 with hG'0 | hG'0
        · exact absurd (by rw [this, hG'0, neg_zero]) hd0
        rw [this, FltWs24.RowF2.ord_neg' K]
        exact hG'F z hz
      rcases eq_or_ne G' 0 with hG'0 | hG'0
      · rw [show d = G by rw [hd, hG'0, sub_zero]]
        exact neg_le_ord_of_mem_riemannRochSpace hG hG0 z
      have h1 := neg_le_ord_of_mem_riemannRochSpace hG hG0 z
      have h2 := hG'F z hz
      have h3 := min_ord_le_ord_add z (f := G) (g := -G') (by rw [← sub_eq_add_neg]; exact hd0) hG0 (neg_ne_zero.mpr hG'0)
      rw [FltWs24.RowF2.ord_neg' K, ← sub_eq_add_neg] at h3
      exact le_trans (le_min h1 h2) h3
    have hL : ∀ z : SSIndex p N K hp5 (2 * (m : ℤ)), lead N K z.1 (poleOrder p N K hp5 (2 * (m : ℤ)) z) d = 0 := by
      intro z
      have hratz := isRational K N z.1
      have hmemG : unif N K z.1 ^ poleOrder p N K hp5 (2 * (m : ℤ)) z * G ∈ z.1.toValuationSubring := by
        refine zpow_mul_mem_of_le K N z.1 _ ?_
        rcases eq_or_ne G 0 with hG0 | hG0
        · exact Or.inl hG0
        · right; rw [← hDx z]; exact neg_le_ord_of_mem_riemannRochSpace hG hG0 z.1
      have hmemG' : unif N K z.1 ^ poleOrder p N K hp5 (2 * (m : ℤ)) z * G' ∈ z.1.toValuationSubring := by
        refine zpow_mul_mem_of_le K N z.1 _ ?_
        rcases eq_or_ne G' 0 with hG'0 | hG'0
        · exact Or.inl hG'0
        · right; rw [← hDx z]; exact hG'F z.1 z.2.1
      have hneg : unif N K z.1 ^ poleOrder p N K hp5 (2 * (m : ℤ)) z * (-G') ∈ z.1.toValuationSubring := by
        rw [mul_neg]; exact neg_mem hmemG'
      unfold lead
      rw [hd, sub_eq_add_neg, mul_add, FltWs24.RowF2.evalAt_add' K z.1 hratz hmemG hneg, mul_neg,
        FltWs24.RowF2.evalAt_neg' K z.1 hratz hmemG']
      have := hG'L z
      unfold lead at this
      rw [this, hv]
      unfold lead
      ring

    set S := Place.fiberAlong (heckeAlphaC K N ℓ) hαu x.1 with hSdef
    have hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hαu = x.1 := fun y => Place.mem_fiberAlong
    obtain ⟨hH, hW, hS⟩ := ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
      p hp5 K N ℓ hN hℓN hℓp hαu hβu x.1 x.2.1 S hSx
    have hceil := ModularCurve.neg_mul_poleOrder_add_one_le_ord_heckeBetaC_mul_pow p hp5 K N ℓ hN hℓN hℓp hαu hβu
      m hm h hh0 d hd0 hF hL x S hSx (by rw [hhm]; exact hH) hW hS

    have hΘ0 : (heckeBetaC K N ℓ) d * h ^ m ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hd0) (pow_ne_zero _ hh0)
    have hvan : x.1.evalAt (π ^ a * Td) = 0 := by
      refine evalAt_zpow_mul_trace_eq_zero p K N ℓ hN hℓN hℓK x.1 π a _ ?_
      intro Y hY
      have hYS : Y ∈ S := (hSx Y).mpr hY
      have h1 := hceil Y hYS
      have hπa : (heckeAlphaC K N ℓ) (π ^ a) ≠ 0 := (map_ne_zero _).mpr (zpow_ne_zero a (unif_ne_zero K N x.1))
      rw [Y.ord_mul hπa hΘ0, map_zpow₀, Place.ord_zpow, Place.ord_restrictAlong (heckeAlphaC K N ℓ) hαu Y π, hY, ord_unif K N x.1, mul_one]
      linarith

    have ha0 : 0 ≤ a := by
      rw [ha, ← hDx x, weightDivisor_ss_m p K N hp5 hpN m x.1 x.2.1]
      have hW1 : (1 : ℤ) ≤ (jWidth (x.1.evalAt (jGeomGen K N)) : ℤ) := by
        have : 1 ≤ jWidth (x.1.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> norm_num
        exact_mod_cast this
      exact Int.ediv_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    have hfloor := Place.neg_le_ord_trace_of_forall_le_ord (heckeAlphaC K N ℓ) hαu hfin hsep x.1 S hSx a ha0 ((heckeBetaC K N ℓ) d * h ^ m)
      (fun Y hY => by have := hceil Y hY; linarith)
    refine ⟨hvan, zpow_mul_mem_of_le K N x.1 a ?_⟩
    rcases eq_or_ne Td 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr hfloor

  have hTG'_mem : π ^ a * TG' ∈ x.1.toValuationSubring := by
    have : π ^ a * TG' = π ^ a * TG - π ^ a * Td := by rw [hsplit]; ring
    rw [this]
    exact sub_mem hTG_mem hTd.2
  have hlead : lead N K x.1 a TG = lead N K x.1 a TG' := by
    unfold lead
    rw [hsplit, mul_add, FltWs24.RowF2.evalAt_add' K x.1 hrat hTG'_mem hTd.2, hTd.1, add_zero]

  have hconst_mem : algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) ∈ x.1.toValuationSubring := x.1.algebraMap_mem' _
  show lead N K x.1 a (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) * TG) = (ℓ : K) ^ (m - 1) * lead N K x.1 a TG'
  unfold lead
  rw [mul_left_comm, Place.evalAt_mul x.1 hrat hconst_mem hTG_mem, Place.evalAt_algebraMap]
  unfold lead at hlead
  rw [hlead]

end S_ModularCurve_SSHeckeV2_lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map (solution)
