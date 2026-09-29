-- Prove2me | solution 1 for ModularCurve.exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8539bf8c-9d54-5d56-87cc-e133e9190db7

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_SwdAlgebra
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
import Theorems.Thm_ModPForms_modPMod_le_modPMod_of_dvd
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
import Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace BSemi

theorem ofPowerSeries_heckeV (K : Type) [Field K] (ℓ : ℕ) [NeZero ℓ] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.heckeV ℓ φ) = qExpand K ℓ (HahnSeries.ofPowerSeries ℤ K φ) := by
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  ext k
  cases k with
  | negSucc n =>

    rw [PowerSeries.coeff_coe, if_pos (Int.negSucc_lt_zero n)]
    by_cases hdvd : (ℓ : ℤ) ∣ Int.negSucc n
    · obtain ⟨k', hk'⟩ := hdvd
      rw [hk', qExpand_coeff_mul, PowerSeries.coeff_coe, if_pos]
      by_contra hcon
      have : 0 ≤ (ℓ : ℤ) * k' := mul_nonneg hℓpos.le (le_of_not_gt hcon)
      rw [← hk'] at this
      exact absurd this (not_le.2 (Int.negSucc_lt_zero n))
    · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd]
  | ofNat n =>
    rw [Int.ofNat_eq_coe, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_heckeV]
    by_cases hdvd : ℓ ∣ n
    · obtain ⟨n', rfl⟩ := hdvd
      rw [if_pos (dvd_mul_right ℓ n'), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ)),
        Nat.cast_mul, qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff]
    · rw [if_neg hdvd, qExpand_coeff_of_not_dvd ℓ _ (by exact_mod_cast hdvd)]

theorem stackOrd_mul {K : Type} [Field K] [DecidableEq K] (N : ℕ) [NeZero N] (a b : ℤ)
    (X Y : ↥(modularFunctionFieldC K N)) (hX : X ≠ 0) (hY : Y ≠ 0) (x : Place K (modularFunctionFieldC K N)) :
    stackOrd N (a + b) (X * Y) x = stackOrd N a X x + stackOrd N b Y x := by
  unfold stackOrd
  rw [x.ord_mul hX hY]
  ring

section Psi

variable (p : ℕ) [hp : Fact p.Prime] (M : ℕ) [NeZero M] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (K : Type) [Field K] [CharP K p]

def psi : PowerSeries K := (ℓ : K) • ((ℓ : K) • PowerSeries.heckeV ℓ (SwdAlgebra.qP K) - SwdAlgebra.qP K)

theorem psi_mem (hℓM : ℓ ∣ M) : psi ℓ K ∈ ModPForms.modPMod M 2 K :=
  ModPForms.modPMod_le_modPMod_of_dvd ℓ M hℓM 2 K
    (Submodule.smul_mem _ _ (ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod ℓ K))

theorem ofPowerSeries_psi :
    HahnSeries.ofPowerSeries ℤ K (psi ℓ K)
      = (ℓ : K) ^ 2 • qExpand K ℓ (HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
          - (ℓ : K) • HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) := by
  simp only [psi, smul_sub, smul_smul, ← sq, map_sub, LinearMap.map_smul_of_tower, ← ofPowerSeries_heckeV]
  rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, map_mul, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul]

theorem coeff_one_qP : PowerSeries.coeff 1 (SwdAlgebra.qP K) = ((-24 : ℤ) : K) := by
  simp only [SwdAlgebra.qP, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, one_ne_zero, if_false,
    Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, mul_one]

theorem coeff_one_heckeV_qP : PowerSeries.coeff 1 (PowerSeries.heckeV ℓ (SwdAlgebra.qP K)) = 0 := by
  rw [PowerSeries.coeff_heckeV, if_neg]
  intro h
  exact hℓ.out.one_lt.ne' (Nat.dvd_one.1 h)

include hp in
theorem psi_ne_zero (hp5 : 5 ≤ p) (hℓp : ℓ ≠ p) : psi ℓ K ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [psi, map_smul, map_sub, map_smul, coeff_one_heckeV_qP, coeff_one_qP, smul_zero, zero_sub, smul_eq_mul,
    map_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · have : ((ℓ : ℕ) : K) = 0 := h1
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 this).symm
  · rw [neg_eq_zero, Int.cast_neg, neg_eq_zero] at h1
    have h24 : ((24 : ℕ) : K) = 0 := by exact_mod_cast h1
    rw [CharP.cast_eq_zero_iff K p] at h24
    have : p ≤ 24 := Nat.le_of_dvd (by norm_num) h24

    have h24' : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24'] at h24
    rcases (Nat.Prime.dvd_mul hp.out).mp h24 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega

end Psi

theorem main (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ℓ ∣ M)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    ∃ Ψ : ↥(modularFunctionFieldC K M),
      (Ψ : LaurentSeries K) =
          ((ℓ : K) ^ 2 • qExpand K ℓ (HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
              - (ℓ : K) • HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
            * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) ∧
      ∀ y : Place K (modularFunctionFieldC K M), IsAffineGeomPlace K M y → y ∈ ssPlaces p M K →
          1 ≤ stackOrd M (((p : ℤ) + 1) / 2) Ψ y := by

  obtain ⟨t, ht⟩ : ∃ t : ℕ, p = 2 * t + 1 := by
    obtain ⟨t, ht⟩ := hp.out.eq_two_or_odd'.resolve_left (by omega)
    exact ⟨t, by omega⟩
  have hpm1 : ((p : ℤ) - 1) / 2 = t := by omega
  have hpp1 : ((p : ℤ) + 1) / 2 = t + 1 := by omega
  set T : LaurentSeries K := thetaL K (jqModC K) with hT

  have hψmem : psi ℓ K ∈ ModPForms.modPMod M (2 * ((1 : ℕ) : ℤ)) K := by simpa using psi_mem M ℓ K hℓM
  obtain ⟨G, hGint, hGq⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p M hpM K 1 _ hψmem
  obtain ⟨h, hhq, hhaff, -⟩ := ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 M hpM K
  have hT0 : T ≠ 0 := by
    have h1 := ModularCurve.thetaL_jqNModC_ne_zero K 1 (by simp)
    rwa [jqNModC_one] at h1
  have hGq' : (G : LaurentSeries K) * T = HahnSeries.ofPowerSeries ℤ K (psi ℓ K) := by
    simpa [qexpOfWeight, thetaJ, ← hT] using hGq
  have hG0 : G ≠ 0 := by
    intro h0
    apply psi_ne_zero p ℓ K hp5 hℓp
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [← hGq', h0, ZeroMemClass.coe_zero, zero_mul, map_zero]
  have hh0 : h ≠ 0 := by
    intro h0; have e := congrArg Subtype.val h0; rw [hhq] at e
    exact zpow_ne_zero _ hT0 (by simpa using e)
  refine ⟨G * h, ?_, ?_⟩
  · rw [IntermediateField.coe_mul, hhq, ← hT, ← ofPowerSeries_psi, ← hGq', hpm1, hpp1, mul_assoc]
    congr 1
    rw [show (-((t : ℤ) + 1)) = (-1 : ℤ) + (-(t : ℤ)) by ring, zpow_add₀ hT0, zpow_neg_one, ← mul_assoc,
      mul_inv_cancel₀ hT0, one_mul]
  · intro y hy hss
    obtain ⟨hGaff, -⟩ := ModularCurve.stackOrd_nonneg_and_le_ord_of_isModPFormFn p hp5 M hpM K 1 G hG0 hGint
    have e : stackOrd M (((p : ℤ) + 1) / 2) (G * h) y = stackOrd M (1 : ℤ) G y + stackOrd M (((p : ℤ) - 1) / 2) h y := by
      rw [hpp1, hpm1, show ((t : ℤ) + 1) = 1 + (t : ℤ) by ring]
      exact stackOrd_mul M 1 t G h hG0 hh0 y
    rw [e, (hhaff y hy).1 hss]
    have := hGaff y hy
    push_cast at this
    linarith

end BSemi

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ℓ ∣ M)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    ∃ Ψ : ↥(modularFunctionFieldC K M),
      (Ψ : LaurentSeries K) =
          ((ℓ : K) ^ 2 • qExpand K ℓ (HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
              - (ℓ : K) • HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K))
            * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) ∧
      ∀ y : Place K (modularFunctionFieldC K M), IsAffineGeomPlace K M y → y ∈ ssPlaces p M K →
          1 ≤ stackOrd M (((p : ℤ) + 1) / 2) Ψ y :=
  BSemi.main p hp5 M hpM ℓ hℓp hℓM K

end S_ModularCurve_exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd
end P2MW
export P2MW.S_ModularCurve_exists_coe_eq_qExpand_qP_sub_mul_thetaL_zpow_and_one_le_stackOrd (solution)
