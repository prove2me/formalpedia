-- Prove2me | solution 1 for ModPForms.exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4fa32eb6-2b83-593f-af55-3aa376a32a4c

import Definitions.Def_ModularCurve_SSCarrier3
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"
set_option autoImplicit false

namespace ResMulThree

open ModularCurve ModularCurve.SSCarrier3 AlgebraicCurve

private theorem coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  rcases lt_or_ge (n + 1) 0 with h | h
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, jNum_eq_pow_three, map_pow]
    apply coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [coeff_thetaL, HahnSeries.coeff_neg]
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
  · rw [coeff_jqModC K h, mul_zero, neg_zero]

variable {F : Type} [Field F] {N' : ℕ} [NeZero N']

private theorem ord_jGeomGen_pos (x : ssPlaces3 F N') : 0 < x.1.ord (jGeomGen F N') := x.2

private theorem jGeomGen_ne_zero (x : ssPlaces3 F N') : jGeomGen F N' ≠ 0 := by
  intro h
  have key : ∀ v : Place F ↥(modularFunctionFieldC F N'), jGeomGen F N' = 0 → v.ord (jGeomGen F N') = 0 := by
    intro v hv
    rw [hv]
    simp
  have h0 := key x.1 h
  have hx := ord_jGeomGen_pos x
  omega

private theorem neg_jGeomGen_ne_zero (x : ssPlaces3 F N') :
    (-(jGeomGen F N') : ↥(modularFunctionFieldC F N')) ≠ 0 :=
  neg_ne_zero.mpr (jGeomGen_ne_zero x)

private theorem ord_neg (x : ssPlaces3 F N') (f : ↥(modularFunctionFieldC F N')) :
    x.1.ord (-f) = x.1.ord f := by
  simp [Place.ord, Valuation.map_neg]

private theorem _root_.ResMulThree.exists_irreducible (x : ssPlaces3 F N') :
    ∃ π₀ : x.1.toValuationSubring, Irreducible π₀ :=
  IsDiscreteValuationRing.exists_irreducible _

p2m_export "ResMulThree" "exists_irreducible"
private theorem ord_uniformizer (x : ssPlaces3 F N') : x.1.ord (uniformizer x) = 1 := by
  obtain ⟨π₀, hπ₀⟩ := exists_irreducible x
  exact Classical.epsilon_spec (p := fun π : ↥(modularFunctionFieldC F N') => x.1.ord π = 1)
    ⟨(π₀ : ↥(modularFunctionFieldC F N')), x.1.ord_coe_irreducible hπ₀⟩

private theorem uniformizer_ne_zero (x : ssPlaces3 F N') : uniformizer x ≠ 0 := by
  intro h
  have h1 := ord_uniformizer x
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

private theorem ord_pow (x : ssPlaces3 F N') (f : ↥(modularFunctionFieldC F N')) (n : ℕ) :
    x.1.ord (f ^ n) = n * x.1.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

private theorem mem_of_ord_nonneg (x : ssPlaces3 F N') {f : ↥(modularFunctionFieldC F N')} (hf : f ≠ 0)
    (h : 0 ≤ x.1.ord f) : f ∈ x.1.toValuationSubring := by
  obtain ⟨π₀, hπ₀⟩ := exists_irreducible x
  obtain ⟨u, hu⟩ := x.1.exists_unit_mul_zpow hf hπ₀
  rw [hu]
  refine mul_mem (u : x.1.toValuationSubring).2 ?_
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hn, zpow_natCast]
  exact pow_mem π₀.2 n

private theorem exists_unit_of_ord_eq_zero (x : ssPlaces3 F N') {f : ↥(modularFunctionFieldC F N')}
    (hf : f ≠ 0) (h : x.1.ord f = 0) :
    ∃ u : x.1.toValuationSubringˣ, ((u : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) = f := by
  obtain ⟨π₀, hπ₀⟩ := exists_irreducible x
  obtain ⟨u, hu⟩ := x.1.exists_unit_mul_zpow hf hπ₀
  refine ⟨u, ?_⟩
  rw [hu, h, zpow_zero, mul_one]

private theorem ord_nonneg_of_mem (x : ssPlaces3 F N') {f : ↥(modularFunctionFieldC F N')} (hf : f ≠ 0)
    (h : f ∈ x.1.toValuationSubring) : 0 ≤ x.1.ord f := by
  obtain ⟨π₀, hπ₀⟩ := exists_irreducible x
  obtain ⟨u, hu⟩ := x.1.exists_unit_mul_zpow hf hπ₀
  rcases le_or_gt 0 (x.1.ord f) with hpos | hneg
  · exact hpos
  exfalso
  set n : ℕ := (-(x.1.ord f)).toNat with hn
  have hn' : x.1.ord f = -(n : ℤ) := by omega
  have hn0 : n ≠ 0 := by omega
  have hπ₀C : ((π₀ : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ₀.ne_zero
  have hf' : f = ((u : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N'))
      * (((π₀ : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) ^ n)⁻¹ := by
    conv_lhs => rw [hu]
    rw [hn', zpow_neg, zpow_natCast]

  have hvu : (((u⁻¹ : x.1.toValuationSubringˣ) : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N'))
      * ((u : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) = 1 := by
    have h1 : ((u⁻¹ : x.1.toValuationSubringˣ) : x.1.toValuationSubring) * (u : x.1.toValuationSubring) = 1 :=
      u.inv_mul
    have h2 : ((((u⁻¹ : x.1.toValuationSubringˣ) : x.1.toValuationSubring) * (u : x.1.toValuationSubring)
        : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N'))
        = ((1 : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) := by
      rw [h1]
    push_cast at h2
    exact h2
  have hinv : ((((π₀ : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) ^ n)⁻¹)
      ∈ x.1.toValuationSubring := by
    have heq : (((π₀ : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) ^ n)⁻¹
        = (((u⁻¹ : x.1.toValuationSubringˣ) : x.1.toValuationSubring) : ↥(modularFunctionFieldC F N')) * f := by
      rw [hf', ← mul_assoc, hvu, one_mul]
    rw [heq]
    exact mul_mem ((u⁻¹ : x.1.toValuationSubringˣ) : x.1.toValuationSubring).2 h
  have hunit : IsUnit (π₀ ^ n) := by
    rw [isUnit_iff_exists_inv]
    refine ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero n hπ₀C)
  exact hπ₀.not_isUnit ((isUnit_pow_iff hn0).mp hunit)

private theorem aPole_eq (m : ℕ) (x : ssPlaces3 F N') :
    aPole m x = 7 * (m : ℤ) * x.1.ord (jGeomGen F N') / 6 + 1 := rfl

private theorem aPole_pos (m : ℕ) (x : ssPlaces3 F N') : 0 < aPole m x := by
  have hx := x.2
  rw [aPole_eq]
  have : 0 ≤ 7 * (m : ℤ) * x.1.ord (jGeomGen F N') / 6 := by positivity
  omega

private theorem toNat_aPole_add_two (m : ℕ) (x : ssPlaces3 F N')
    (he : x.1.ord (jGeomGen F N') = 3 ∨ x.1.ord (jGeomGen F N') = 6) :
    (aPole (m + 2) x).toNat = (aPole 1 x).toNat + (aPole m x).toNat + (x.1.ord (jGeomGen F N')).toNat := by
  simp only [aPole_eq]
  push_cast
  rcases he with he | he <;> rw [he] <;> omega

variable [CharP F 3]

private theorem coe_neg_jGeomGen :
    (((-(jGeomGen F N') : ↥(modularFunctionFieldC F N')) : LaurentSeries F)) = thetaJ F := by
  rw [thetaJ, thetaL_jqModC_eq_neg]
  simp [coe_jGeomGen]

private theorem thetaJ_ne_zero (x : ssPlaces3 F N') : thetaJ F ≠ 0 := by
  rw [← coe_neg_jGeomGen (F := F) (N' := N')]
  intro h
  apply jGeomGen_ne_zero x
  have h' : (-(jGeomGen F N') : ↥(modularFunctionFieldC F N')) = 0 := by
    exact_mod_cast h
  exact neg_eq_zero.mp h'

private theorem witness_unique (x : ssPlaces3 F N') (m : ℕ) {G₁ G₂ : ↥(modularFunctionFieldC F N')}
    {φ : PowerSeries F}
    (h₁ : (G₁ : LaurentSeries F) * thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ)
    (h₂ : (G₂ : LaurentSeries F) * thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ) : G₁ = G₂ := by
  have hθ : thetaJ F ^ m ≠ 0 := pow_ne_zero m (thetaJ_ne_zero x)
  have h : (G₁ : LaurentSeries F) = G₂ := mul_right_cancel₀ hθ (h₁.trans h₂.symm)
  exact_mod_cast h

open Classical in
private theorem res_eq_of_witness (x : ssPlaces3 F N') (m : ℕ) (φ : PowerSeries F)
    (G : ↥(modularFunctionFieldC F N'))
    (hG : (G : LaurentSeries F) * thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ) :
    res m φ x = if hm : G * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring then
      IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩ else 0 := by
  have h : ∃ G : ↥(modularFunctionFieldC F N'),
      (G : LaurentSeries F) * thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ := ⟨G, hG⟩
  have hchoose : Classical.choose h = G := witness_unique x m (Classical.choose_spec h) hG
  have key : ∀ G₀ : ↥(modularFunctionFieldC F N'), G₀ = G →
      (if hm : G₀ * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring then
        IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩ else 0)
      = (if hm : G * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring then
        IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩ else 0) := by
    rintro G₀ rfl
    rfl
  unfold res
  rw [dif_pos h]
  exact key _ hchoose

open Classical in
private theorem res_eq_residue (x : ssPlaces3 F N') (m : ℕ) (φ : PowerSeries F)
    (G : ↥(modularFunctionFieldC F N'))
    (hG : (G : LaurentSeries F) * thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ)
    (hm : G * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring) :
    res m φ x = IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩ := by
  rw [res_eq_of_witness x m φ G hG, dif_pos hm]

omit [CharP F 3] in

private theorem exists_preimage_of_mem_adjoin (x : ssPlaces3 F N') {y : LaurentSeries F}
    (hy : y ∈ Algebra.adjoin F ({jqModC F} : Set (LaurentSeries F))) :
    ∃ o : x.1.toValuationSubring, ((o : ↥(modularFunctionFieldC F N')) : LaurentSeries F) = y := by
  have hJ : jGeomGen F N' ∈ x.1.toValuationSubring :=
    mem_of_ord_nonneg x (jGeomGen_ne_zero x) (ord_jGeomGen_pos x).le
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨⟨jGeomGen F N', hJ⟩, by simp [coe_jGeomGen]⟩
  | algebraMap a => exact ⟨algebraMap F x.1.toValuationSubring a, rfl⟩
  | add z w _ _ hz hw =>
    obtain ⟨o₁, h₁⟩ := hz
    obtain ⟨o₂, h₂⟩ := hw
    refine ⟨o₁ + o₂, ?_⟩
    push_cast
    rw [h₁, h₂]
  | mul z w _ _ hz hw =>
    obtain ⟨o₁, h₁⟩ := hz
    obtain ⟨o₂, h₂⟩ := hw
    refine ⟨o₁ * o₂, ?_⟩
    push_cast
    rw [h₁, h₂]

omit [CharP F 3] in

private theorem mem_of_isIntegral_adjoin (x : ssPlaces3 F N') (H : ↥(modularFunctionFieldC F N'))
    (hH : IsIntegral (Algebra.adjoin F ({jqModC F} : Set (LaurentSeries F))) (H : LaurentSeries F)) :
    H ∈ x.1.toValuationSubring := by
  obtain ⟨p, hpm, hp⟩ := hH
  set g : x.1.toValuationSubring →+* LaurentSeries F :=
    ((modularFunctionFieldC F N').val.toRingHom).comp
      (algebraMap x.1.toValuationSubring ↥(modularFunctionFieldC F N')) with hg
  have hlift : p.map (algebraMap _ (LaurentSeries F)) ∈ Polynomial.lifts g := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨o, ho⟩ := exists_preimage_of_mem_adjoin x (p.coeff n).2
    exact ⟨o, ho⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hpm.map _)
  have hint : IsIntegral x.1.toValuationSubring H := by
    refine ⟨q, hqm, ?_⟩
    apply Subtype.val_injective
    show (modularFunctionFieldC F N').val.toRingHom (Polynomial.eval₂ (algebraMap _ _) H q)
      = ((0 : ↥(modularFunctionFieldC F N')) : LaurentSeries F)
    rw [Polynomial.hom_eval₂, ← hg, ← Polynomial.eval_map, hq, Polynomial.eval_map, ZeroMemClass.coe_zero]
    exact hp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem six_mul_ord_add_nonneg (x : ssPlaces3 F N') (k : ℕ) (G : ↥(modularFunctionFieldC F N'))
    (hG0 : G ≠ 0) (hG : IsModPFormFn F k (G : LaurentSeries F)) :
    0 ≤ 6 * x.1.ord G + 7 * (k : ℤ) * x.1.ord (jGeomGen F N') := by
  obtain ⟨h₁, -⟩ := hG
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h1728 : algebraMap F (LaurentSeries F) 1728 = 0 := by
    rw [show (1728 : F) = 3 * 576 by norm_num, h3, zero_mul, map_zero]
  have hcoe : ((G ^ 6 * jGeomGen F N' ^ (7 * k) : ↥(modularFunctionFieldC F N')) : LaurentSeries F)
      = (G : LaurentSeries F) ^ 6 * jqModC F ^ (4 * k)
        * (jqModC F - algebraMap F (LaurentSeries F) 1728) ^ (3 * k) := by
    rw [h1728, sub_zero]
    push_cast
    rw [coe_jGeomGen]
    ring
  have hHint : IsIntegral (Algebra.adjoin F ({jqModC F} : Set (LaurentSeries F)))
      ((G ^ 6 * jGeomGen F N' ^ (7 * k) : ↥(modularFunctionFieldC F N')) : LaurentSeries F) := by
    rw [hcoe]
    exact h₁
  have hmem := mem_of_isIntegral_adjoin x _ hHint
  have hG6 : G ^ 6 ≠ 0 := pow_ne_zero _ hG0
  have hJ7 : jGeomGen F N' ^ (7 * k) ≠ 0 := pow_ne_zero _ (jGeomGen_ne_zero x)
  have hord := ord_nonneg_of_mem x (mul_ne_zero hG6 hJ7) hmem
  rw [x.1.ord_mul hG6 hJ7, ord_pow, ord_pow] at hord
  push_cast at hord
  linarith

private theorem exists_witness_mem (hpN' : ¬ 3 ∣ N') (x : ssPlaces3 F N')
    (he : x.1.ord (jGeomGen F N') = 3 ∨ x.1.ord (jGeomGen F N') = 6) (j : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' (2 * ((j + 1 : ℕ) : ℤ)) F) :
    ∃ G : ↥(modularFunctionFieldC F N'),
      (G : LaurentSeries F) * thetaJ F ^ j = HahnSeries.ofPowerSeries ℤ F φ ∧
      G * uniformizer x ^ (aPole j x).toNat ∈ x.1.toValuationSubring := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨G', hG'int, hG'⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod (p := 3) (N := N') hpN' (K := F)
      (m := j + 1) φ hφ
  rw [qexpOfWeight, zpow_natCast] at hG'
  refine ⟨G' * (-(jGeomGen F N')), ?_, ?_⟩
  · have hc : ((G' * (-(jGeomGen F N')) : ↥(modularFunctionFieldC F N')) : LaurentSeries F)
        = (G' : LaurentSeries F) * thetaJ F := by
      rw [← coe_neg_jGeomGen (N' := N')]
      rfl
    rw [hc, mul_assoc, ← pow_succ', hG']
  · by_cases hG'0 : G' = 0
    · subst hG'0
      simp
    have hb := six_mul_ord_add_nonneg x (j + 1) G' hG'0 hG'int
    have hπ := ord_uniformizer x
    have hne : G' * (-(jGeomGen F N')) * uniformizer x ^ (aPole j x).toNat ≠ 0 :=
      mul_ne_zero (mul_ne_zero hG'0 (neg_jGeomGen_ne_zero x)) (pow_ne_zero _ (uniformizer_ne_zero x))
    apply mem_of_ord_nonneg x hne
    rw [x.1.ord_mul (mul_ne_zero hG'0 (neg_jGeomGen_ne_zero x)) (pow_ne_zero _ (uniformizer_ne_zero x)),
      x.1.ord_mul hG'0 (neg_jGeomGen_ne_zero x), ord_neg, ord_pow, hπ, mul_one]
    have hpos := aPole_pos j x
    rw [Int.toNat_of_nonneg hpos.le]
    rw [aPole_eq] at hpos ⊢
    push_cast at hb
    rcases he with he | he <;> rw [he] at hb ⊢ <;> omega

omit [CharP F 3] in
private theorem unitElt_ne_zero (x : ssPlaces3 F N') :
    uniformizer x ^ (x.1.ord (jGeomGen F N')).toNat * (-(jGeomGen F N'))⁻¹ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (uniformizer_ne_zero x)) (inv_ne_zero (neg_jGeomGen_ne_zero x))

omit [CharP F 3] in
private theorem ord_unitElt (x : ssPlaces3 F N') :
    x.1.ord (uniformizer x ^ (x.1.ord (jGeomGen F N')).toNat * (-(jGeomGen F N'))⁻¹) = 0 := by
  rw [x.1.ord_mul (pow_ne_zero _ (uniformizer_ne_zero x)) (inv_ne_zero (neg_jGeomGen_ne_zero x)),
    ord_pow, ord_uniformizer, Place.ord_inv, ord_neg, Int.toNat_of_nonneg (ord_jGeomGen_pos x).le]
  omega

omit [CharP F 3] in
private noncomputable def unitOf (x : ssPlaces3 F N') : x.1.toValuationSubringˣ :=
  Classical.choose (exists_unit_of_ord_eq_zero x (unitElt_ne_zero x) (ord_unitElt x))

omit [CharP F 3] in
private theorem coe_unitOf (x : ssPlaces3 F N') :
    (((unitOf x : x.1.toValuationSubring)) : ↥(modularFunctionFieldC F N'))
      = uniformizer x ^ (x.1.ord (jGeomGen F N')).toNat * (-(jGeomGen F N'))⁻¹ :=
  Classical.choose_spec (exists_unit_of_ord_eq_zero x (unitElt_ne_zero x) (ord_unitElt x))

omit [CharP F 3] in

private noncomputable def cval (x : ssPlaces3 F N') : x.1.ResidueField :=
  IsLocalRing.residue x.1.toValuationSubring (unitOf x : x.1.toValuationSubring)

omit [CharP F 3] in
private theorem cval_ne_zero (x : ssPlaces3 F N') : cval x ≠ 0 := by
  unfold cval
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (unitOf x).isUnit

private theorem main (hpN' : ¬ 3 ∣ N') (x : ssPlaces3 F N')
    (he : x.1.ord (jGeomGen F N') = 3 ∨ x.1.ord (jGeomGen F N') = 6) (m : ℕ) (ψ φ : PowerSeries F)
    (hψ : ψ ∈ ModPForms.modPMod N' 4 F) (hφ : φ ∈ ModPForms.modPMod N' (2 * (m : ℤ) + 2) F) :
    res (m + 2) (ψ * φ) x = cval x * res 1 ψ x * res m φ x := by
  have hψ' : ψ ∈ ModPForms.modPMod N' (2 * ((1 + 1 : ℕ) : ℤ)) F := by norm_num; exact hψ
  have hφ' : φ ∈ ModPForms.modPMod N' (2 * ((m + 1 : ℕ) : ℤ)) F := by push_cast; ring_nf; ring_nf at hφ; exact hφ
  obtain ⟨Gψ, hGψ, hAψ⟩ := exists_witness_mem hpN' x he 1 ψ hψ'
  obtain ⟨Gφ, hGφ, hAφ⟩ := exists_witness_mem hpN' x he m φ hφ'
  set t : ↥(modularFunctionFieldC F N') := -(jGeomGen F N') with ht
  have ht0 : t ≠ 0 := neg_jGeomGen_ne_zero x
  have htc : (t : LaurentSeries F) = thetaJ F := coe_neg_jGeomGen

  have hGp : ((Gψ * Gφ * t⁻¹ : ↥(modularFunctionFieldC F N')) : LaurentSeries F) * thetaJ F ^ (m + 2)
      = HahnSeries.ofPowerSeries ℤ F (ψ * φ) := by
    push_cast
    rw [htc, ← hGψ, ← hGφ]
    have hθ : thetaJ F ≠ 0 := thetaJ_ne_zero x
    field_simp
    ring

  have hsplit : Gψ * Gφ * t⁻¹ * uniformizer x ^ (aPole (m + 2) x).toNat
      = (Gψ * uniformizer x ^ (aPole 1 x).toNat) * (Gφ * uniformizer x ^ (aPole m x).toNat)
        * (uniformizer x ^ (x.1.ord (jGeomGen F N')).toNat * t⁻¹) := by
    rw [toNat_aPole_add_two m x he, pow_add, pow_add]
    ring
  have hU : uniformizer x ^ (x.1.ord (jGeomGen F N')).toNat * t⁻¹ ∈ x.1.toValuationSubring := by
    rw [← coe_unitOf x]
    exact ((unitOf x : x.1.toValuationSubring)).2
  have hAp : Gψ * Gφ * t⁻¹ * uniformizer x ^ (aPole (m + 2) x).toNat ∈ x.1.toValuationSubring := by
    rw [hsplit]
    exact mul_mem (mul_mem hAψ hAφ) hU
  rw [res_eq_residue x (m + 2) (ψ * φ) _ hGp hAp, res_eq_residue x 1 ψ Gψ hGψ hAψ,
    res_eq_residue x m φ Gφ hGφ hAφ]
  unfold cval
  have hprod : (⟨_, hAp⟩ : x.1.toValuationSubring)
      = (unitOf x : x.1.toValuationSubring) * ⟨_, hAψ⟩ * ⟨_, hAφ⟩ := by
    apply Subtype.ext
    change Gψ * Gφ * t⁻¹ * uniformizer x ^ (aPole (m + 2) x).toNat
      = (((unitOf x : x.1.toValuationSubring)) : ↥(modularFunctionFieldC F N'))
        * (Gψ * uniformizer x ^ (aPole 1 x).toNat) * (Gφ * uniformizer x ^ (aPole m x).toNat)
    rw [coe_unitOf x, hsplit]
    ring
  rw [hprod, map_mul, map_mul]

end ResMulThree

open ModPForms in
theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    ∃ c : (x : ModularCurve.ssPlaces3 F N') → x.1.ResidueField, (∀ x, c x ≠ 0) ∧
      ∀ (m : ℕ) (ψ φ : PowerSeries F), ψ ∈ modPMod N' 4 F → φ ∈ modPMod N' (2 * (m : ℤ) + 2) F →
        ∀ x : ModularCurve.ssPlaces3 F N',
          ModularCurve.SSCarrier3.res (m + 2) (ψ * φ) x =
            c x * ModularCurve.SSCarrier3.res 1 ψ x * ModularCurve.SSCarrier3.res m φ x := by
  refine ⟨fun x => ResMulThree.cval x, fun x => ResMulThree.cval_ne_zero x, ?_⟩
  intro m ψ φ hψ hφ x
  have he := ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
    N' hpN' hε F x.1 x.2
  exact ResMulThree.main hpN' x he m ψ φ hψ hφ

end S_ModPForms_exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
end P2MW
export P2MW.S_ModPForms_exists_forall_res_mul_eq_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed (solution)
