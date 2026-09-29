-- Prove2me | solution 1 for ModPForms.res_eq_zero_of_mem_modPMod_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/48edab47-09cc-5beb-8f1d-50f675343ddd

import Definitions.Def_ModularCurve_SSCarrier3
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_res_eq_zero_of_mem_modPMod_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false

private theorem k1le_thetaJ3_coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem k1le_thetaJ3_jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem k1le_thetaJ3_coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  by_cases h : n + 1 < 0
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, k1le_thetaJ3_jNum_eq_pow_three, map_pow]
    apply k1le_thetaJ3_coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem k1le_thetaJ3_coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem k1le_thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [k1le_thetaJ3_coeff_thetaL, HahnSeries.coeff_neg]
  by_cases h : (3 : ℤ) ∣ n + 1
  · obtain ⟨c, hc⟩ := h
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have hn : (n : K) = -1 := by
      have hn' : n = 3 * c - 1 := by omega
      rw [hn']
      push_cast
      rw [h3]
      ring
    rw [hn, neg_one_mul]
  · rw [k1le_thetaJ3_coeff_jqModC K h, mul_zero, neg_zero]

private theorem k1le_char (F : Type) [Field F] [CharP F 3] : (1728 : F) = 0 := by
  have h : ((1728 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 1728).mpr (by norm_num)
  exact_mod_cast h

private noncomputable def k1le_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) :
    Algebra.adjoin K ({t} : Set E) ≃ₐ[K] Algebra.adjoin K ({(t : L)} : Set L) :=
  (Subalgebra.equivMapOfInjective (Algebra.adjoin K ({t} : Set E)) E.val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, Set.image_singleton]; rfl))

private theorem k1le_coe_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) (a : Algebra.adjoin K ({t} : Set E)) :
    ((k1le_adjoinEquiv E t a : Algebra.adjoin K ({(t : L)} : Set L)) : L) = ((a : E) : L) :=
  rfl

private theorem k1le_isIntegral_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t u : E)
    (hu : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (u : L)) :
    IsIntegral (Algebra.adjoin K ({t} : Set E)) u := by
  have h1 : IsIntegral (Algebra.adjoin K ({t} : Set E)) (u : L) := by
    refine IsIntegral.map_of_comp_eq (k1le_adjoinEquiv E t).symm.toAlgHom.toRingHom (RingHom.id L) ?_ hu
    refine RingHom.ext fun b => ?_
    have hb := k1le_coe_adjoinEquiv E t ((k1le_adjoinEquiv E t).symm b)
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb.symm
  haveI : IsScalarTower (Algebra.adjoin K ({t} : Set E)) E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({t} : Set E)) E L)
    (algebraMap E L).injective).mp h1

private theorem k1le_ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    {a : E} (ha : a ≠ 0) (i : ℕ) : x.ord (a ^ i) = (i : ℤ) * x.ord a := by
  have _ := ha
  rw [← zpow_natCast, x.ord_zpow]

private theorem k1le_thetaJ_ne_zero (F : Type) [Field F] [CharP F 3] : ModularCurve.thetaJ F ≠ 0 := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := k1le_thetaL_jqModC_eq_neg F
  rw [hθ, neg_ne_zero]
  exact ModularCurve.jqModC_ne_zero_def F

private theorem k1le_ord_bound (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (G : ↥(ModularCurve.modularFunctionFieldC F N')) (hG0 : G ≠ 0)
    (hfn : ModularCurve.IsModPFormFn F m (G : LaurentSeries F))
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N') := by
  have hjne : ModularCurve.jqModC F ≠ 0 := ModularCurve.jqModC_ne_zero_def F
  have hj0 : ModularCurve.jGeomGen F N' ≠ 0 := by
    intro h
    apply hjne
    have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
    simpa using h'
  have h1728 : algebraMap F (LaurentSeries F) (1728 : F) = 0 := by rw [k1le_char F, map_zero]
  unfold ModularCurve.IsModPFormFn at hfn
  obtain ⟨h1, -⟩ := hfn
  simp only [h1728, sub_zero] at h1
  have hY : IsIntegral
      (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
      (G ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * m) * ModularCurve.jGeomGen F N' ^ (3 * m)) := by
    apply k1le_isIntegral_of_coe
    push_cast
    exact h1
  have hYord := x.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg hY hx.le
  rw [x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), k1le_ord_pow x hG0, k1le_ord_pow x hj0, k1le_ord_pow x hj0]
    at hYord
  push_cast at hYord
  linarith

private theorem k1le_residue_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (f : E) (hf : 1 ≤ x.ord f) (hmem : f ∈ x.toValuationSubring) :
    IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hv : x.adicValuation f = 1 := (x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).2 hu
  have h0 : x.ord f = 0 := by simp [AlgebraicCurve.Place.ord, hv]
  omega

private theorem k1le_ord_uniformizer (N' : ℕ) [NeZero N'] (F : Type) [Field F] (x : ModularCurve.ssPlaces3 F N') :
    x.1.ord (ModularCurve.SSCarrier3.uniformizer x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.1.toValuationSubring
  unfold ModularCurve.SSCarrier3.uniformizer
  exact Classical.epsilon_spec
    (⟨(π : ↥(ModularCurve.modularFunctionFieldC F N')), x.1.ord_coe_irreducible hπ⟩ :
      ∃ ϖ : ↥(ModularCurve.modularFunctionFieldC F N'), x.1.ord ϖ = 1)

private theorem k1le_branch (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (x : ModularCurve.ssPlaces3 F N') (g : ↥(ModularCurve.modularFunctionFieldC F N'))
    (hfn : ModularCurve.IsModPFormFn F m (g : LaurentSeries F))
    (hmem : g * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole m x).toNat ∈
      x.1.toValuationSubring) :
    IsLocalRing.residue x.1.toValuationSubring ⟨_, hmem⟩ = 0 := by
  by_cases hg : g = 0
  · subst hg
    have h0 : (⟨_, hmem⟩ : x.1.toValuationSubring) = 0 := Subtype.ext (by simp)
    rw [h0, map_zero]
  · apply k1le_residue_eq_zero
    have hπ1 := k1le_ord_uniformizer N' F x
    have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
      intro h0
      rw [h0, x.1.ord_zero] at hπ1
      exact zero_ne_one hπ1
    have hA : 0 ≤ 7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') :=
      mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg m)) x.2.le
    have hbound := k1le_ord_bound N' F m g hg hfn x.1 x.2
    have hn : (((ModularCurve.SSCarrier3.aPole m x).toNat : ℕ) : ℤ) = ModularCurve.SSCarrier3.aPole m x := by
      apply Int.toNat_of_nonneg
      unfold ModularCurve.SSCarrier3.aPole
      omega
    rw [x.1.ord_mul hg (pow_ne_zero _ hπ0), k1le_ord_pow x.1 hπ0, hπ1, mul_one, hn]
    unfold ModularCurve.SSCarrier3.aPole
    omega

open ModPForms in
theorem solution (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ modPMod N' (2 * (m : ℤ)) F) (x : ModularCurve.ssPlaces3 F N') :
    ModularCurve.SSCarrier3.res m φ x = 0 := by
  have _ := hε
  obtain ⟨G₁, hfn, hq⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod 3 N' hpN' F m φ hφ
  have hq' : (G₁ : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ := by
    have h := hq
    unfold ModularCurve.qexpOfWeight at h
    rwa [zpow_natCast] at h
  unfold ModularCurve.SSCarrier3.res
  by_cases h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ
  · rw [dif_pos h]
    have hspec := Classical.choose_spec h
    have hcoe : ((Classical.choose h : ↥(ModularCurve.modularFunctionFieldC F N')) : LaurentSeries F)
        = (G₁ : LaurentSeries F) :=
      mul_right_cancel₀ (pow_ne_zero m (k1le_thetaJ_ne_zero F)) (hspec.trans hq'.symm)
    have hfn' : ModularCurve.IsModPFormFn F m ((Classical.choose h : ↥(ModularCurve.modularFunctionFieldC F N')) :
        LaurentSeries F) := by
      rw [hcoe]
      exact hfn
    split_ifs with hm
    · exact k1le_branch N' F m x (Classical.choose h) hfn' hm
    · rfl
  · rw [dif_neg h]

end S_ModPForms_res_eq_zero_of_mem_modPMod_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_res_eq_zero_of_mem_modPMod_of_exists_prime_dvd_mod_three_eq_two (solution)
