-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.ssHeckeFun_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/89c6a614-c528-51ca-a6be-c1cc97d837af

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_lead_trace_eq_zero_of_forall_le_ord
import Theorems.Thm_ModularCurve_neg_mul_poleOrder_add_one_le_ord_heckeBetaC_mul_pow
import Theorems.Thm_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
import Theorems.Thm_ModularCurve_SSHeckeV2_liftFun_spec
import Theorems.Thm_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
import Theorems.Thm_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
import Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_ModularCurve_ord_unif
import Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_ssHeckeFun_smul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV"
p2m_attr_erase "simp" "LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSHeckeV2_ssHeckeFun_smul.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "SSIndex SSCarrier poleOrder unif lead ssPlaces jGeomGen modularFunctionFieldC jWidth heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC weightDivisor weightDivisor_apply lead_trace_eq_zero_of_forall_le_ord neg_mul_poleOrder_add_one_le_ord_heckeBetaC_mul_pow neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow SSHeckeV2.liftFun_spec SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber finiteAlong_heckeAlphaC separableAlong_heckeAlphaC_heckeBetaC heckeAlphaCIntegral_unconditional heckeBetaCIntegral_unconditional isCurveOver_modularFunctionFieldC_of_perfectField charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul modularFunctionFieldC_eq_modularFunctionFieldFullC ord_unif weightFloor_eq_of_isAffineGeomPlace exists_divisor_forall_eq_weightFloor_fieldC"
namespace SSHLin
p2m_open "ModularCurve"

variable {K : Type} [Field K]

theorem evalAt_add' {F : Type*} [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  have hfg : f + g ∈ v.toValuationSubring := add_mem hf hg
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hfg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  rw [show (⟨f + g, hfg⟩ : v.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl, map_add]

variable (N : ℕ) [NeZero N]

theorem zpow_mul_mem (x : Place K ↥(modularFunctionFieldC K N)) (a : ℤ) (t : ↥(modularFunctionFieldC K N)) (ht : t = 0 ∨ -a ≤ x.ord t) :
    ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [mul_zero]; exact zero_mem _
  rcases ht with h | h
  · exact absurd h ht0
  have hπ := ModularCurve.ord_unif K N x
  have hπ0 : ModularCurve.unif N K x ≠ 0 := by intro h0; rw [h0, Place.ord_zero] at hπ; exact zero_ne_one hπ
  apply Place.mem_of_ord_nonneg x (mul_ne_zero (zpow_ne_zero a hπ0) ht0)
  rw [x.ord_mul (zpow_ne_zero a hπ0) ht0, x.ord_zpow, hπ, mul_one]; omega

theorem lead_add (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (a : ℤ) (s t : ↥(modularFunctionFieldC K N))
    (hs : ModularCurve.unif N K x ^ a * s ∈ x.toValuationSubring) (ht : ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring) :
    ModularCurve.lead N K x a (s + t) = ModularCurve.lead N K x a s + ModularCurve.lead N K x a t := by
  unfold ModularCurve.lead
  rw [mul_add, evalAt_add' x hx hs ht]

theorem lead_algebraMap_mul (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (a : ℤ) (c : K) (t : ↥(modularFunctionFieldC K N))
    (ht : ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring) :
    ModularCurve.lead N K x a (algebraMap K _ c * t) = c * ModularCurve.lead N K x a t := by
  unfold ModularCurve.lead
  rw [mul_left_comm, Place.evalAt_mul x hx (x.algebraMap_mem' c) ht, Place.evalAt_algebraMap]

end ModularCurve.SSHLin

open ModularCurve.SSHLin in
theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (k : ℤ) (c : K) (v : ModularCurve.SSCarrier p N K hp5 k) :
    ModularCurve.ssHeckeFun p N K hp5 k ℓ (c • v) = c • ModularCurve.ssHeckeFun p N K hp5 k ℓ v := by
  classical
  funext x

  obtain ⟨hxss, hk2, hkev, hxdvd, -⟩ := x.2
  obtain ⟨m, hkm⟩ : ∃ m : ℕ, k = 2 * (m : ℤ) := by
    obtain ⟨c, hc⟩ := hkev
    exact ⟨c.toNat, by rw [Int.toNat_of_nonneg (by omega)]; exact hc⟩
  subst hkm
  have hm : 1 ≤ m := by omega
  have hkn : ((2 * (m : ℤ)) / 2).toNat = m := by simp
  have hk1 : (2 * (m : ℤ)) / 2 - 1 = (m : ℤ) - 1 := by simp
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  have hpNℓ : ¬ p ∣ N * ℓ := by
    intro hh
    rcases (Nat.Prime.dvd_mul Fact.out).mp hh with h1 | h2
    · exact hpN h1
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h2).symm

  have hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral := ModularCurve.heckeAlphaCIntegral_unconditional K N ℓ
  have hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral := ModularCurve.heckeBetaCIntegral_unconditional K N ℓ
  have hfin := ModularCurve.finiteAlong_heckeAlphaC K N ℓ
  have hsep := (ModularCurve.separableAlong_heckeAlphaC_heckeBetaC K N ℓ hpNℓ).1

  haveI hF : IsCurveOver K ↥(modularFunctionFieldC K N) := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField K N
  have hroof : charLDegeneracyRoof K N ℓ = modularFunctionFieldC K (N * ℓ) := by
    rw [ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNℓ,
      ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p (N * ℓ) hpNℓ]
  haveI hR : IsCurveOver K ↥(charLDegeneracyRoof K N ℓ) := by
    rw [hroof]; exact ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField K (N * ℓ)
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)

  have hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1 ↔
      y.restrictAlong (heckeAlphaC K N ℓ) hα = x.1 := fun y => AlgebraicCurve.Place.mem_fiberAlong
  obtain ⟨hH, hW, hS⟩ := ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
    p hp5 K N ℓ hN hℓN hℓp hα hβ x.1 hxss (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx
  have hxrat : x.1.IsRational := hxss.1

  have ha0 : 0 ≤ ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x := by
    unfold ModularCurve.poleOrder
    apply Int.ediv_nonneg _ (by positivity)
    apply mul_nonneg (by omega)
    have : 1 ≤ jWidth (x.1.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> omega
    omega

  have hLspec := fun u : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)) =>
    ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) u
  simp only [hkn] at hLspec

  show algebraMap K K ((ℓ : K) ^ ((2 * (m : ℤ)) / 2 - 1)) * ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x)
      (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) (c • v))
        * ModularCurve.heckeMultiplier N K ℓ ^ ((2 * (m : ℤ)) / 2).toNat))
    = c * (algebraMap K K ((ℓ : K) ^ ((2 * (m : ℤ)) / 2 - 1)) * ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x)
      (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)
        * ModularCurve.heckeMultiplier N K ℓ ^ ((2 * (m : ℤ)) / 2).toNat)))
  rw [mul_left_comm, hkn]
  congr 1
  set a := ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x with hadef
  set hM := ModularCurve.heckeMultiplier N K ℓ with hMdef
  set L3 := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) (c • v)
  set L1 := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v
  set d : ↥(modularFunctionFieldC K N) := L3 - algebraMap K _ c * L1 with hddef
  let Tr : ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N) := fun t => Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ t * hM ^ m)
  have hTr_add : ∀ s t : ↥(modularFunctionFieldC K N), Tr (s + t) = Tr s + Tr t := by
    intro s t; show Algebra.trace _ _ _ = Algebra.trace _ _ _ + Algebra.trace _ _ _
    rw [map_add, add_mul, map_add]
  have hTr_smul : ∀ t : ↥(modularFunctionFieldC K N), Tr (algebraMap K _ c * t) = algebraMap K _ c * Tr t := by
    intro t; show Algebra.trace _ _ _ = algebraMap K _ c * Algebra.trace _ _ _
    have e1 : heckeBetaC K N ℓ (algebraMap K ↥(modularFunctionFieldC K N) c * t) * hM ^ m
        = (algebraMap K ↥(modularFunctionFieldC K N) c) • (heckeBetaC K N ℓ t * hM ^ m) := by
      rw [map_mul, AlgHom.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) c, mul_assoc]
    rw [e1, LinearMap.map_smul_of_tower, smul_eq_mul]
  have hTr3 : Tr L3 = algebraMap K _ c * Tr L1 + Tr d := by
    have : L3 = algebraMap K _ c * L1 + d := by rw [hddef]; abel
    rw [this, hTr_add, hTr_smul]
  show ModularCurve.lead N K x.1 a (Tr L3) = c * ModularCurve.lead N K x.1 a (Tr L1)

  by_cases hM0 : hM = 0
  · have hTr0 : ∀ t, Tr t = 0 := by
      intro t; show Algebra.trace _ _ _ = 0
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
      rw [hM0, pow_succ, mul_zero, mul_zero, map_zero]
    rw [hTr0, hTr0]
    unfold ModularCurve.lead
    rw [mul_zero, show (0 : ↥(modularFunctionFieldC K N)) = algebraMap K _ 0 from (map_zero _).symm, Place.evalAt_algebraMap, mul_zero]

  have memTr : ∀ t : ↥(modularFunctionFieldC K N), (∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K →
      (t = 0 ∨ -(ModularCurve.weightDivisor K N m z) ≤ z.ord t)) →
      ModularCurve.unif N K x.1 ^ a * Tr t ∈ x.1.toValuationSubring := by
    intro t hFt
    apply zpow_mul_mem N x.1 a
    rcases eq_or_ne t 0 with rfl | ht0
    · left; show Algebra.trace _ _ _ = 0; rw [map_zero, zero_mul, map_zero]
    right
    have hFt' : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → -(ModularCurve.weightDivisor K N m z) ≤ z.ord t := by
      intro z hz; rcases hFt z hz with h | h
      · exact absurd h ht0
      · exact h
    have hfl := ModularCurve.neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow p hp5 K N ℓ hN hℓN hℓp hα hβ m hm hM hM0 t ht0 hFt'
      x (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx hH hW hS
    exact AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord (heckeAlphaC K N ℓ) hα hfin hsep x.1
      (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx a ha0 (heckeBetaC K N ℓ t * hM ^ m) hfl

  have vfl : ∀ (z : Place K ↥(modularFunctionFieldC K N)) (D : ℤ) (t : ↥(modularFunctionFieldC K N)), (t = 0 ∨ -D ≤ z.ord t) ↔ z.adicValuation t ≤ WithZero.exp D :=
    fun z D t => z.adicValuation_le_exp_iff.symm
  have hF1 : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → (L1 = 0 ∨ -(ModularCurve.weightDivisor K N m z) ≤ z.ord L1) :=
    fun z hz => Or.inr ((hLspec v).1 z hz)
  have hF3 : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → (L3 = 0 ∨ -(ModularCurve.weightDivisor K N m z) ≤ z.ord L3) :=
    fun z hz => Or.inr ((hLspec (c • v)).1 z hz)
  have hFc : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K →
      (algebraMap K _ c * L1 = 0 ∨ -(ModularCurve.weightDivisor K N m z) ≤ z.ord (algebraMap K _ c * L1)) := by
    intro z hz
    rw [vfl, map_mul]
    exact (mul_le_of_le_one_left' (z.adicValuation_algebraMap_le_one c)).trans ((vfl z _ L1).mp (hF1 z hz))
  have hFd : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K →
      (d = 0 ∨ -(ModularCurve.weightDivisor K N m z) ≤ z.ord d) := by
    intro z hz
    rw [vfl, hddef, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans (max_le ((vfl z _ L3).mp (hF3 z hz)) ?_)
    rw [Valuation.map_neg]; exact (vfl z _ _).mp (hFc z hz)
  have mem1 := memTr L1 hF1
  have memc := memTr _ hFc
  have memd := memTr d hFd

  have hex := ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m
  have hcoef : ∀ z : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)),
      ModularCurve.weightDivisor K N m z.1 = ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z := by
    intro z
    rw [ModularCurve.weightDivisor_apply K N m hex z.1, ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K m z.1 z.2.1.2.1]
    unfold ModularCurve.poleOrder
    congr 1
    congr 1
    omega
  have memAt : ∀ (z : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))) (t : ↥(modularFunctionFieldC K N)),
      (∀ z' : Place K ↥(modularFunctionFieldC K N), z' ∈ ssPlaces p N K → (t = 0 ∨ -(ModularCurve.weightDivisor K N m z') ≤ z'.ord t)) →
      ModularCurve.unif N K z.1 ^ ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z * t ∈ z.1.toValuationSubring := by
    intro z t ht
    apply zpow_mul_mem N z.1
    rw [← hcoef z]; exact ht z.1 z.2.1

  have hL : ∀ z : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)),
      ModularCurve.lead N K z.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z) d = 0 := by
    intro z
    have hz : z.1.IsRational := z.2.1.1
    have e3 := (hLspec (c • v)).2 z
    have e1 := (hLspec v).2 z
    have hsum : L3 = algebraMap K _ c * L1 + d := by rw [hddef]; abel
    have key : ModularCurve.lead N K z.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z) L3
        = c * ModularCurve.lead N K z.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z) L1
          + ModularCurve.lead N K z.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) z) d := by
      rw [hsum, lead_add N z.1 hz _ _ _ (memAt z _ hFc) (memAt z _ hFd), lead_algebraMap_mul N z.1 hz _ c L1 (memAt z _ hF1)]
    rw [e3, e1] at key
    have : (c • v) z = c * v z := rfl
    rw [this] at key
    linear_combination -key

  have hZ : ModularCurve.lead N K x.1 a (Tr d) = 0 := by
    by_cases hd0 : d = 0
    · have : Tr d = 0 := by show Algebra.trace _ _ _ = 0; rw [hd0, map_zero, zero_mul, map_zero]
      rw [this]; unfold ModularCurve.lead
      rw [mul_zero, show (0 : ↥(modularFunctionFieldC K N)) = algebraMap K _ 0 from (map_zero _).symm, Place.evalAt_algebraMap]
    have hFd' : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → -(ModularCurve.weightDivisor K N m z) ≤ z.ord d := by
      intro z hz; rcases hFd z hz with h | h
      · exact absurd h hd0
      · exact h
    have hΘ := ModularCurve.neg_mul_poleOrder_add_one_le_ord_heckeBetaC_mul_pow p hp5 K N ℓ hN hℓN hℓp hα hβ m hm hM hM0 d hd0 hFd' hL
      x (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx hH hW hS
    exact ModularCurve.lead_trace_eq_zero_of_forall_le_ord p hp5 K N ℓ hα m x
      (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx
      (fun a' g hg => AlgebraicCurve.Place.trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
        (heckeAlphaC K N ℓ) hα hfin hsep x.1 (AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hα x.1) hSx a' g hg)
      (heckeBetaC K N ℓ d * hM ^ m) hΘ

  have memc' : ModularCurve.unif N K x.1 ^ a * (algebraMap K _ c * Tr L1) ∈ x.1.toValuationSubring := by
    rw [← hTr_smul]; exact memc
  rw [hTr3, lead_add N x.1 hxrat a _ _ memc' memd, lead_algebraMap_mul N x.1 hxrat a c _ mem1, hZ, add_zero]

end S_ModularCurve_SSHeckeV2_ssHeckeFun_smul
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_ssHeckeFun_smul (solution)
