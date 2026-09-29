-- Prove2me | solution 1 for ModularCurve.neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/33c15104-38da-516b-a3d3-d1d7e9127ca3

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

noncomputable section

namespace StarRoof

variable (K : Type) [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K]

theorem placeWidth_dvd (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (z : Place K ↥(modularFunctionFieldC K M)) (hz : z ∈ ssPlaces p M K) :
    (placeWidth M z : ℤ) ∣ ((p : ℤ) + 1) / 2 := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  obtain ⟨hrat, haff, hss⟩ := hz
  set a₀ := z.evalAt (jGeomGen K M) with ha₀
  set e := placeRamificationJ M z with he
  have hepos : 0 < e := by
    have h := ord_sub_evalAt_pos_of_isRational hrat haff.1 (jGeomGen_sub_algebraMap_ne_zero K M (z.evalAt (jGeomGen K M)))
    rw [he]; unfold placeRamificationJ; omega
  have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpM hepos
  have hWn : placeWidth M z * e = jWidth a₀ := by
    unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
  by_cases h0 : a₀ = 0
  · rw [jWidth_of_eq_zero h0] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 ⟨e, hWn.symm⟩ with hu1 | hu3
    · rw [hu1]; simp
    · have hmem : (0 : K) ∈ ssJSet p K := by rw [← h0, ha₀]; exact hss
      have hp3 := (zero_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu3]; push_cast; omega
  by_cases hs : a₀ = 1728
  · rw [jWidth_of_eq_1728 hs h0] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).1 ⟨e, hWn.symm⟩ with hu1 | hu2
    · rw [hu1]; simp
    · have hmem : (1728 : K) ∈ ssJSet p K := by rw [← hs, ha₀]; exact hss
      have hp4 := (ofNat1728_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu2]; push_cast; omega
  · rw [jWidth_of_ne h0 hs] at hWn
    rw [Nat.eq_one_of_mul_eq_one_right hWn]; simp

theorem natCast_pow_succ_p (ℓ : ℕ) : ((ℓ : K)) ^ (p + 1) = (ℓ : K) ^ 2 := by
  rw [pow_succ, sq]
  congr 1
  have h := map_natCast (frobenius K p) ℓ
  rwa [frobenius_def] at h

theorem star_gen (hp5 : 5 ≤ p) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (S : IntermediateField K (LaurentSeries K))
    (hS : S = (haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩; modularFunctionFieldC K (N * ℓ)))
    (ψα ψβ : ↥(modularFunctionFieldC K N) →ₐ[K] ↥S)
    (hψα : ∀ x, ((ψα x : ↥S) : LaurentSeries K) = x) (hψβ : ∀ x, ((ψβ x : ↥S) : LaurentSeries K) = qExpand K ℓ x)
    (hα : ψα.toRingHom.IsIntegral) (hβ : ψβ.toRingHom.IsIntegral)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (h : ↥S) (hh : ((h : ↥S) : LaurentSeries K) * thetaL K (jqModC K) = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)))
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (y : Place K ↥S) (hy : y.restrictAlong ψα hα = x) :
    -((Place.ramificationIndexAlong ψα y : ℤ)
        * ((((p : ℤ) + 1) / 2) * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N x : ℤ))) + 1
      ≤ y.ord (algebraMap K ↥S ((ℓ : K) ^ ((p + 1) / 2)) * ψβ b * h ^ ((p + 1) / 2) - algebraMap K ↥S (ℓ : K) * ψα b) := by
  subst hS
  classical
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  have hpN : ¬ p ∣ N := fun h' => hN ((CharP.cast_eq_zero_iff K p N).2 h')
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h'; have := (CharP.cast_eq_zero_iff K p ℓ).1 h'
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 this).symm
  have hNl : ((N * ℓ : ℕ) : K) ≠ 0 := by push_cast; exact mul_ne_zero hN hℓK
  have hpNl : ¬ p ∣ N * ℓ := fun h' => hNl ((CharP.cast_eq_zero_iff K p _).2 h')
  set t : ℕ := (p + 1) / 2 with ht
  have htZ : ((p : ℤ) + 1) / 2 = (t : ℤ) := by omega
  have h2t : 2 * t = p + 1 := by omega

  set θ : LaurentSeries K := thetaL K (jqModC K) with hθ
  have hθ0 : θ ≠ 0 := by
    have h1 := ModularCurve.thetaL_jqNModC_ne_zero K 1 (by simp); rwa [jqNModC_one] at h1
  have hqθ0 : qExpand K ℓ θ ≠ 0 := fun h0 => hθ0 (qExpand_injective (R := K) ℓ (by rw [h0, map_zero]))

  set Φ : ↥(modularFunctionFieldC K (N * ℓ)) :=
    algebraMap K _ ((ℓ : K) ^ t) * ψβ b * h ^ t - algebraMap K _ (ℓ : K) * ψα b with hΦ
  have hhC : (h : LaurentSeries K) = HahnSeries.C (ℓ : K) * qExpand K ℓ θ * θ⁻¹ := by
    rw [HahnSeries.C_mul_eq_smul, ← hh, mul_assoc, mul_inv_cancel₀ hθ0, mul_one]
  have hl2 : ((ℓ : K) ^ t) * (ℓ : K) ^ t = (ℓ : K) ^ 2 := by rw [← pow_add, ← two_mul, h2t, natCast_pow_succ_p K p ℓ]
  have hcoeΦ : (Φ : LaurentSeries K)
      = ((ℓ : K) ^ 2 • qExpand K ℓ (HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
          - (ℓ : K) • HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K)) * θ ^ (-(((p : ℤ) + 1) / 2)) := by
    have eC : ∀ c : K, ((algebraMap K ↥(modularFunctionFieldC K (N * ℓ)) c : ↥(modularFunctionFieldC K (N * ℓ))) : LaurentSeries K)
        = HahnSeries.C c := fun c => by
      rw [SubalgebraClass.coe_algebraMap, ModularCurve.algebraMap_laurentSeries_apply_eq_single, HahnSeries.C_apply]
    have e1 := eC ((ℓ : K) ^ t)
    have e2 := eC (ℓ : K)
    rw [hΦ, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hψβ, hψα, e1, e2, hb, hhC,
      map_mul, map_zpow₀, htZ, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
      show HahnSeries.C ((ℓ : K) ^ 2) = HahnSeries.C ((ℓ : K) ^ t) * (HahnSeries.C (ℓ : K)) ^ t by rw [← map_pow, ← map_mul, hl2]]
    have hθt : θ ^ t ≠ 0 := pow_ne_zero _ hθ0
    have hqθt : qExpand K ℓ θ ^ t ≠ 0 := pow_ne_zero _ hqθ0
    have hii : θ ^ t * θ⁻¹ ^ t = 1 := by rw [← mul_pow, mul_inv_cancel₀ hθ0, one_pow]
    field_simp
    linear_combination (HahnSeries.C ((ℓ : K) ^ t) * (qExpand K ℓ) ((HahnSeries.ofPowerSeries ℤ K) (SwdAlgebra.qP K)) * HahnSeries.C (ℓ : K) ^ t * (qExpand K ℓ) θ ^ t) * hii

  obtain ⟨Ψ, hΨ, hΨss⟩ := exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd p hp5 (N * ℓ) hpNl ℓ hℓp
    (dvd_mul_left ℓ N) K
  have hΦΨ : Φ = Ψ := Subtype.ext (hcoeΦ.trans hΨ.symm)

  have H := degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected N ℓ p hℓ.out hℓp hpN hℓN (k := K)
    ![ψα, ψβ] (fun i => by fin_cases i <;> assumption) hψα hψβ
  obtain ⟨-, -, -, hpres, hrefl⟩ := H
  have hyss : y ∈ ssPlaces p (N * ℓ) K := hrefl 0 _ (hy ▸ hx) y hy
  obtain ⟨hyrat, hyaff, hyssv⟩ := hyss

  have hst : 1 ≤ stackOrd (N * ℓ) (((p : ℤ) + 1) / 2) Φ y := by
    rw [hΦΨ]; exact hΨss y hyaff ⟨hyrat, hyaff, hyssv⟩

  haveI : Fintype ↥(ssPlaces p (N * ℓ) K) := (ssPlaces_finite p (N * ℓ) K).fintype
  haveI : Fintype ↥(ssPlaces p N K) := (ssPlaces_finite p N K).fintype
  let φ : Fin 2 → (↥(modularFunctionFieldC K N) →ₐ[K] ↥(modularFunctionFieldC K (N * ℓ))) := ![ψα, ψβ]
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral := fun i => by fin_cases i <;> assumption
  let ab : Fin 2 → ↥(ssPlaces p (N * ℓ) K) → ↥(ssPlaces p N K) :=
    fun i P => ⟨Place.restrictAlong (φ i) (hφ i) P.1, hpres i P.1 P.2⟩
  let mm : Fin 2 → ↥(ssPlaces p (N * ℓ) K) → ℕ := fun i P => Place.ramificationIndexAlong (φ i) P.1
  have HW := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le N ℓ p hℓ.out hp5 hℓp hpN
    (k := K) ab mm φ hφ hψα hψβ (fun i P => rfl) (fun i P => rfl)
  have hepos : 0 < placeRamificationJ (N * ℓ) y := by
    have h' := ord_sub_evalAt_pos_of_isRational hyrat hyaff.1 (jGeomGen_sub_algebraMap_ne_zero K (N * ℓ) (y.evalAt (jGeomGen K (N * ℓ))))
    unfold placeRamificationJ; omega
  have hdvd : placeRamificationJ (N * ℓ) y ∣ jWidth (y.evalAt (jGeomGen K (N * ℓ))) :=
    placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpNl hepos
  have hWid : Place.ramificationIndexAlong ψα y * placeWidth (N * ℓ) y = placeWidth N x := by
    have := HW 0 ⟨y, hyrat, hyaff, hyssv⟩ hdvd
    rw [← hy]; exact this
  have huy : 0 < placeWidth (N * ℓ) y := by
    have hWpos : 0 < jWidth (y.evalAt (jGeomGen K (N * ℓ))) := by unfold jWidth; split_ifs <;> norm_num
    unfold placeWidth
    exact Nat.div_pos (Nat.le_of_dvd hWpos hdvd) hepos

  have hjval : y.evalAt (jGeomGen K (N * ℓ)) = x.evalAt (jGeomGen K N) := by
    letI := algebraAlong ψα
    haveI := isScalarTower_along ψα
    haveI := isIntegral_along ψα hα
    have hj : jGeomGen K (N * ℓ) = algebraMap ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K (N * ℓ)) (jGeomGen K N) :=
      Subtype.ext (by rw [show algebraMap ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K (N * ℓ)) (jGeomGen K N) = ψα (jGeomGen K N) from rfl, hψα]; rfl)
    have hres : y.restrictAlong ψα hα = y.restrict ↥(modularFunctionFieldC K N) := rfl
    rw [hj, Place.evalAt_algebraMap_eq_evalAt_restrict y (hres ▸ hy ▸ hx.1) (by rw [Place.mem_restrict_iff, ← hj]; exact hyaff.1), ← hres, hy]

  unfold stackOrd at hst
  rw [hjval, htZ] at hst
  set W : ℤ := (jWidth (x.evalAt (jGeomGen K N)) : ℤ) with hW
  set uy : ℤ := (placeWidth (N * ℓ) y : ℤ) with huy'
  set ux : ℤ := (placeWidth N x : ℤ) with hux
  set eα : ℤ := (Place.ramificationIndexAlong ψα y : ℤ) with heα
  have hWidZ : eα * uy = ux := by rw [heα, huy', hux]; exact_mod_cast hWid
  have huypos : 0 < uy := by rw [huy']; exact_mod_cast huy
  have huxdvd : ux ∣ (t : ℤ) := by rw [hux, ← htZ]; exact placeWidth_dvd K p hp5 N hpN x hx
  obtain ⟨c, hc⟩ := huxdvd
  rw [htZ]
  have hux0 : ux ≠ 0 := by
    rw [hux]
    obtain ⟨hxrat, hxaff, -⟩ := hx
    have hexpos : 0 < placeRamificationJ N x := by
      have h' := ord_sub_evalAt_pos_of_isRational hxrat hxaff.1 (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
      unfold placeRamificationJ; omega
    have hxdvd := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hexpos
    have hWpos : 0 < jWidth (x.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> norm_num
    have : 0 < placeWidth N x := by unfold placeWidth; exact Nat.div_pos (Nat.le_of_dvd hWpos hxdvd) hexpos
    exact_mod_cast this.ne'

  have ha' : (t : ℤ) * (W - 1) / ux = c * (W - 1) := by
    rw [hc, mul_assoc, Int.mul_ediv_cancel_left _ hux0]
  rw [ha']

  have htc : (t : ℤ) = eα * uy * c := by rw [hWidZ, hc]
  rw [htc] at hst
  have key : 1 ≤ uy * (y.ord Φ + eα * c * (W - 1)) := by nlinarith [hst]
  have key2 : 1 ≤ y.ord Φ + eα * c * (W - 1) := by
    by_contra hcon
    push_neg at hcon
    have : uy * (y.ord Φ + eα * c * (W - 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos huypos.le (by omega)
    omega
  linarith

include hp in
theorem roof_eq (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime] (hpNl : ¬ p ∣ N * ℓ) :
    charLDegeneracyRoof K N ℓ = (haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩; modularFunctionFieldC K (N * ℓ)) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNl,
    ← modularFunctionFieldC_eq_modularFunctionFieldFullC K p (N * ℓ) hpNl]

end StarRoof

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hh : ((h : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K) = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)))
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x) :
    ∀ y ∈ S,
      -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ)
          * ((((p : ℤ) + 1) / 2) * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N x : ℤ))) + 1
        ≤ y.ord (algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ ((p + 1) / 2)) * heckeBetaC K N ℓ b * h ^ ((p + 1) / 2)
                  - algebraMap K ↥(charLDegeneracyRoof K N ℓ) (ℓ : K) * heckeAlphaC K N ℓ b) := by
  intro y hyS
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0; have := (CharP.cast_eq_zero_iff K p ℓ).1 h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).1 this).symm
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h0; have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h0
    push_cast at this; exact mul_ne_zero hN hℓK this
  exact StarRoof.star_gen K p hp5 N ℓ hN hℓN hℓp _ (StarRoof.roof_eq K p N ℓ hpNl)
    (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ) (coe_heckeAlphaC K N ℓ) (coe_heckeBetaC K N ℓ) hα
    (heckeBetaCIntegral_unconditional K N ℓ) b hb h hh x hx y ((hSx y).1 hyS)

end S_ModularCurve_neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces (solution)
