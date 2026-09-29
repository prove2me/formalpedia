-- Prove2me | solution 1 for ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f5f6bdfc-1d16-5f8e-b356-33ad2f11bd16

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionField
import Theorems.Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
import Theorems.Thm_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure
import Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf"
p2m_attr_erase "simp" "ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve~genus ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace GenusIg3Nu

open ModularCurve

theorem noRoot_of_mod_twelve (ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (x : ZMod ℓ) :
    x ^ 2 + x + 1 ≠ 0 ∧ x ^ 2 + 1 ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx1 : x ≠ 1 := by
      rintro rfl; norm_num at hx
      have : ((3 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast hx
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this; omega
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hx3 : x ^ 3 = 1 := by
      have : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
      rw [hx, mul_zero, sub_eq_zero] at this; exact this
    have hord : orderOf (Units.mk0 x hx0) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · ext; simp [hx3]
      · intro h; apply hx1; have := congrArg Units.val h; simpa using this
    have hdvd : 3 ∣ Fintype.card (ZMod ℓ)ˣ := hord ▸ orderOf_dvd_card
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hℓ] at hdvd
    omega
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hx2 : x ^ 2 = -1 := eq_neg_of_add_eq_zero_left hx
    have hx1 : x ^ 2 ≠ 1 := by
      rw [hx2]; intro h
      have h2 : (2 : ZMod ℓ) = 0 := by linear_combination -h
      have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this; omega
    have hx4 : x ^ 4 = 1 := by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; ring
    have hord : orderOf (Units.mk0 x hx0) = 4 := by
      refine (orderOf_eq_iff (by norm_num)).2 ⟨by ext; simp [hx4], fun m hm hm0 h => ?_⟩
      have hm' : (x : ZMod ℓ) ^ m = 1 := by have := congrArg Units.val h; simpa using this
      interval_cases m
      · apply hx1; rw [pow_one] at hm'; rw [hm']; ring
      · exact hx1 hm'
      · have : x ^ 4 = x := by rw [pow_succ, hm', one_mul]
        rw [hx4] at this
        apply hx1; rw [← this]; ring
    have hdvd : 4 ∣ Fintype.card (ZMod ℓ)ˣ := hord ▸ orderOf_dvd_card
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hℓ] at hdvd
    omega

theorem nuTwo_eq_zero_of_dvd (M' ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M') :
    nuTwo M' = 0 := by
  unfold nuTwo
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, hx⟩ => ?_⟩
  have := congrArg (ZMod.castHom hℓM' (ZMod ℓ)) hx
  simp only [map_add, map_pow, map_one, map_zero] at this
  exact (noRoot_of_mod_twelve ℓ hℓ h12 _).2 this

theorem nuThree_eq_zero_of_dvd (M' ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M') :
    nuThree M' = 0 := by
  unfold nuThree
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, hx⟩ => ?_⟩
  have := congrArg (ZMod.castHom hℓM' (ZMod ℓ)) hx
  simp only [map_add, map_pow, map_one, map_zero] at this
  exact (noRoot_of_mod_twelve ℓ hℓ h12 _).1 this

end GenusIg3Nu
namespace GenusIg3Aux

theorem finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem nonempty_ringHom_residueField (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] :
    Nonempty (ResidueField A →+* κ) := by
  haveI hch : CharP (ResidueField A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  letI : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  letI : Algebra (ZMod q) κ := ZMod.algebra _ q
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic (ZMod q) (ResidueField A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A q
  let ψ : ResidueField A →ₐ[ZMod q] κ := IsAlgClosed.lift
  exact ⟨ψ.toRingHom⟩

theorem genusFF_xHFunctionFieldC_levelH_eq_residueField (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] :
    AlgebraicCurve.genusFF κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) =
      AlgebraicCurve.genusFF (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := by
  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hch : CharP (ResidueField A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  obtain ⟨φ⟩ := nonempty_ringHom_residueField q A hA κ
  letI : Algebra (ResidueField A) κ := φ.toAlgebra
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI := finiteIndex_gammaH (q ^ 2 * M') (levelH q M')
  have hT := ModularCurve.translation_mem_GammaH (q ^ 2 * M') (levelH q M')
  haveI h1 : IsCurveOver κ ↥(qExpFunctionFieldC κ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ _ hT
  haveI h2 : IsCurveOver (ResidueField A)
      ↥(qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField A) _ hT
  obtain ⟨x, -, hx, hxf⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ _ hT
  obtain ⟨y, -, hy, hyf⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField A) _ hT
  have h := ModularCurve.genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed
    (ResidueField A) κ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) ⟨y, hy, hyf⟩ ⟨x, hx, hxf⟩
  exact h

end GenusIg3Aux

namespace GenusIg3Aux

theorem genusFF_xHFunctionFieldC_levelH_eq_genusFormula_of_eq_three (q : ℕ) [Fact q.Prime] (hq3 : q = 3)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    (AlgebraicCurve.genusFF (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) : ℚ) =
      genusFormula M' := by
  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hch : CharP (ResidueField A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  rw [ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three q hq3 M' hqM' A hA,
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q M' hqM']
  have hN : ((M' : ℕ) : ResidueField A) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ResidueField A) q] at h
    exact hqM' h
  rw [ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar (ResidueField A) M' hN,
    ModularCurve.modularFunctionFieldBar_eq_modularFunctionFieldC M',
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (AlgebraicClosure ℚ) 0 M'
      (by rw [Nat.zero_dvd]; exact NeZero.ne M'),
    ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure M']

end GenusIg3Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (W : Finset (Place κ (modularFunctionFieldC κ M'))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' κ) :
    (AlgebraicCurve.genusFF κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) : ℚ) =
      1 + ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 48
        - ((q : ℚ) - 1) * cuspCount M' / 4
        - (W.card : ℚ) / 2 := by
  classical
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, Fact.out⟩
  have h6 := ModularCurve.six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd q hq3 M' hqM' ℓ hℓ hℓ12 hℓM' κ W hW
  have h6' : (6 : ℚ) * (W.card : ℚ) = (dedekindPsi M' : ℚ) := by exact_mod_cast h6
  rw [GenusIg3Aux.genusFF_xHFunctionFieldC_levelH_eq_residueField q M' A hA κ,
    GenusIg3Aux.genusFF_xHFunctionFieldC_levelH_eq_genusFormula_of_eq_three q hq3 M' hqM' A hA]
  unfold genusFormula
  rw [GenusIg3Nu.nuTwo_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM', GenusIg3Nu.nuThree_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM']
  subst hq3
  push_cast
  linear_combination (1 / 12 : ℚ) * h6'

end

end S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd (solution)
