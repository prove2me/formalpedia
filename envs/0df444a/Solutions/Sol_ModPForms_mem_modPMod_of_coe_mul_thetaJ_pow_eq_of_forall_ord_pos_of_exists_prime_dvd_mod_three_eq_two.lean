-- Prove2me | solution 1 for ModPForms.mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bf7809df-5f3f-520b-bd7e-3961de1474d1

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
import Theorems.Thm_ModularCurve_isIntegral_adjoin_mk_coeffMap
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_map_algHom
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false

namespace FaceBRed

private theorem fb_ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    {a : E} (ha : a ≠ 0) (i : ℕ) : x.ord (a ^ i) = (i : ℤ) * x.ord a := by
  have _ := ha
  rw [← zpow_natCast, x.ord_zpow]

private theorem fb_ord_neg {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (a : E) : x.ord (-a) = x.ord a := by
  simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]

private theorem fb_ord_nonneg_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E)
    {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem fb_mem_of_ord_nonneg {K E : Type*} [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E)
    {f : E} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem fb_thetaJ3_coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem fb_thetaJ3_jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem fb_thetaJ3_coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  by_cases h : n + 1 < 0
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, fb_thetaJ3_jNum_eq_pow_three, map_pow]
    apply fb_thetaJ3_coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem fb_thetaJ3_coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem fb_thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [fb_thetaJ3_coeff_thetaL, HahnSeries.coeff_neg]
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
  · rw [fb_thetaJ3_coeff_jqModC K h, mul_zero, neg_zero]

private theorem fb_char (F : Type) [Field F] [CharP F 3] : (1728 : F) = 0 := by
  have h : ((1728 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 1728).mpr (by norm_num)
  exact_mod_cast h

private noncomputable def fb_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) :
    Algebra.adjoin K ({t} : Set E) ≃ₐ[K] Algebra.adjoin K ({(t : L)} : Set L) :=
  (Subalgebra.equivMapOfInjective (Algebra.adjoin K ({t} : Set E)) E.val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, Set.image_singleton]; rfl))

private theorem fb_coe_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) (a : Algebra.adjoin K ({t} : Set E)) :
    ((fb_adjoinEquiv E t a : Algebra.adjoin K ({(t : L)} : Set L)) : L) = ((a : E) : L) :=
  rfl

private theorem fb_isIntegral_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t u : E)
    (hu : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (u : L)) :
    IsIntegral (Algebra.adjoin K ({t} : Set E)) u := by
  have h1 : IsIntegral (Algebra.adjoin K ({t} : Set E)) (u : L) := by
    refine IsIntegral.map_of_comp_eq (fb_adjoinEquiv E t).symm.toAlgHom.toRingHom (RingHom.id L) ?_ hu
    refine RingHom.ext fun b => ?_
    have hb := fb_coe_adjoinEquiv E t ((fb_adjoinEquiv E t).symm b)
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb.symm
  haveI : IsScalarTower (Algebra.adjoin K ({t} : Set E)) E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({t} : Set E)) E L)
    (algebraMap E L).injective).mp h1

private theorem fb_thetaJ_ne_zero (F : Type) [Field F] [CharP F 3] : ModularCurve.thetaJ F ≠ 0 := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := fb_thetaL_jqModC_eq_neg F
  rw [hθ, neg_ne_zero]
  exact ModularCurve.jqModC_ne_zero_def F

private theorem fb_jne (F : Type) [Field F] [CharP F 3] (N' : ℕ) [NeZero N'] : ModularCurve.jGeomGen F N' ≠ 0 := by
  intro h
  apply ModularCurve.jqModC_ne_zero_def F
  have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
  simpa using h'

private theorem fb_isIntegral_of_pair {K E : Type*} [Field K] [Field E] [Algebra K E] {j y z : E}
    (hy : IsIntegral (Algebra.adjoin K ({j} : Set E)) y)
    (hz : IsIntegral (Algebra.adjoin K ({j, y} : Set E)) z) :
    IsIntegral (Algebra.adjoin K ({j} : Set E)) z := by
  have hAB : Algebra.adjoin K ({j} : Set E) ≤ Algebra.adjoin K ({j, y} : Set E) :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  letI : Algebra (Algebra.adjoin K ({j} : Set E)) (Algebra.adjoin K ({j, y} : Set E)) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin K ({j} : Set E)) (Algebra.adjoin K ({j, y} : Set E)) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (Algebra.adjoin K ({j} : Set E)) (Algebra.adjoin K ({j, y} : Set E)) := by
    refine ⟨fun b => ?_⟩
    have hfg := hy.fg_adjoin_singleton
    have hle : Algebra.adjoin K ({j, y} : Set E) ≤
        (Algebra.adjoin (Algebra.adjoin K ({j} : Set E)) ({y} : Set E)).restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro x (hx | hx)
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, hx]
        have hjA : j ∈ Algebra.adjoin K ({j} : Set E) := Algebra.subset_adjoin (Set.mem_singleton j)
        have hjT := Subalgebra.algebraMap_mem (Algebra.adjoin (Algebra.adjoin K ({j} : Set E)) ({y} : Set E))
          (⟨j, hjA⟩ : Algebra.adjoin K ({j} : Set E))
        exact hjT
      · rw [Set.mem_singleton_iff] at hx
        rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, hx]
        exact Algebra.subset_adjoin (Set.mem_singleton y)
    have hbE : IsIntegral (Algebra.adjoin K ({j} : Set E)) (b : E) :=
      IsIntegral.of_mem_of_fg _ hfg _ (hle b.2)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({j} : Set E))
      (Algebra.adjoin K ({j, y} : Set E)) E) Subtype.val_injective).mp hbE
  exact isIntegral_trans z hz

private theorem fb_jN_integral (F : Type) [Field F] (N' : ℕ) [NeZero N'] :
    IsIntegral (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
      (ModularCurve.jNGeomGen F N') := by
  have hmem : ModularCurve.coeffMap (Int.castRingHom F) (ModularCurve.jqNModC ℤ N') ∈
      ModularCurve.modularFunctionFieldC F N' := by
    rw [ModularCurve.coeffMap_jqNModC]
    exact ModularCurve.jqNModC_mem F N'
  have h := ModularCurve.isIntegral_adjoin_mk_coeffMap (Int.castRingHom F) N'
    (Polynomial.X : Polynomial (Polynomial ℤ)) (ModularCurve.jqNModC ℤ N')
    (by simp only [Polynomial.map_X, Polynomial.eval_X]) hmem
  have key : (⟨ModularCurve.coeffMap (Int.castRingHom F) (ModularCurve.jqNModC ℤ N'), hmem⟩ :
      ↥(ModularCurve.modularFunctionFieldC F N')) = ModularCurve.jNGeomGen F N' :=
    Subtype.ext (ModularCurve.coeffMap_jqNModC _ _)
  rw [key] at h
  exact h

end FaceBRed

open ModPForms FaceBRed in

theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F) (G : ↥(ModularCurve.modularFunctionFieldC F N'))
    (hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ)
    (hvan : ∀ x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'),
      0 < x.ord (ModularCurve.jGeomGen F N') →
        0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N')) :
    φ ∈ modPMod N' (2 * (m : ℤ)) F  := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ0 : ModularCurve.thetaJ F ≠ 0 := fb_thetaJ_ne_zero F
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := fb_thetaL_jqModC_eq_neg F
  have h1728 : algebraMap F (LaurentSeries F) 1728 = 0 := by rw [fb_char F, map_zero]
  have hj0 : ModularCurve.jGeomGen F N' ≠ 0 := fb_jne F N'

  have hφ' : φ ∈ modPMod N' (2 * ((m + 1 : ℕ) : ℤ)) F := by
    have h2 : (2 * ((m + 1 : ℕ) : ℤ)) = 2 * (m : ℤ) + 2 := by push_cast; ring
    rw [h2]
    exact hφ
  obtain ⟨G', hfn', hq'⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod 3 N' hpN' F (m + 1) φ hφ'
  have hq'' : (G' : LaurentSeries F) * ModularCurve.thetaJ F ^ (m + 1) = HahnSeries.ofPowerSeries ℤ F φ := by
    rw [← hq', ModularCurve.qexpOfWeight, zpow_natCast]

  have hGG' : (G : LaurentSeries F) = G' * ModularCurve.thetaJ F := by
    apply mul_right_cancel₀ (pow_ne_zero m hθ0)
    rw [hG, ← hq'', mul_assoc, ← pow_succ']
  have hGC : G = -(G' * ModularCurve.jGeomGen F N') := by
    apply Subtype.ext
    rw [hGG', hθ]
    push_cast
    simp [ModularCurve.coe_jGeomGen]
  have hG'0 : ∀ _ : G ≠ 0, G' ≠ 0 := fun hG0 h0 => hG0 (by rw [hGC, h0, zero_mul, neg_zero])

  have hfn : ModularCurve.IsModPFormFn F m (G : LaurentSeries F) := by
    obtain ⟨h1', h2'⟩ := hfn'
    refine ⟨?_, ?_⟩
    · simp only [h1728, sub_zero] at h1' ⊢
      have hN : ((N' : ℕ) : F) ≠ 0 := fun h => hpN' ((CharP.cast_eq_zero_iff F 3 N').mp h)
      have hz : IsIntegral
          (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
          (G ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * m) * ModularCurve.jGeomGen F N' ^ (3 * m)) := by
        refine fb_isIntegral_of_pair (fb_jN_integral F N')
          ((ModularCurve.forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin hN _).mp fun u hu => ?_)
        have hju : ModularCurve.jGeomGen F N' ∈ u.toValuationSubring := (show _ ∧ _ from hu).1
        have hordj : 0 ≤ u.ord (ModularCurve.jGeomGen F N') := fb_ord_nonneg_of_mem u hju
        by_cases hG0 : G = 0
        · rw [hG0, zero_pow (by norm_num), zero_mul, zero_mul]
          exact zero_mem _
        apply fb_mem_of_ord_nonneg u
          (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0))
        rw [u.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
          u.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), fb_ord_pow u hG0, fb_ord_pow u hj0, fb_ord_pow u hj0]
        push_cast
        rcases hordj.lt_or_eq with hpos | hzero
        · have hv := hvan u hpos
          linarith
        · have hY : IsIntegral
              (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
              (G' ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * (m + 1)) * ModularCurve.jGeomGen F N' ^ (3 * (m + 1))) := by
            apply fb_isIntegral_of_coe
            push_cast
            exact h1'
          have hYord := u.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg hY hordj
          rw [u.ord_mul (mul_ne_zero (pow_ne_zero _ (hG'0 hG0)) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
            u.ord_mul (pow_ne_zero _ (hG'0 hG0)) (pow_ne_zero _ hj0), fb_ord_pow u (hG'0 hG0), fb_ord_pow u hj0,
            fb_ord_pow u hj0] at hYord
          push_cast at hYord
          have hordG : u.ord G = u.ord G' + u.ord (ModularCurve.jGeomGen F N') := by
            rw [hGC, fb_ord_neg, u.ord_mul (hG'0 hG0) hj0]
          have hj00 : u.ord (ModularCurve.jGeomGen F N') = 0 := hzero.symm
          rw [hordG, hj00]
          rw [hj00] at hYord
          linarith
      have hout := AlgebraicCurve.isIntegral_adjoin_map_algHom (ModularCurve.modularFunctionFieldC F N').val hz
      simp at hout
      exact hout
    · simp only [h1728, sub_zero] at h2' ⊢
      have h2 : (G : LaurentSeries F) ^ 2 * ModularCurve.jqModC F ^ m * ModularCurve.jqModC F ^ m =
          (G' : LaurentSeries F) ^ 2 * ModularCurve.jqModC F ^ (m + 1) * ModularCurve.jqModC F ^ (m + 1) := by
        rw [hGG', hθ]
        ring
      rw [h2]
      exact h2'

  obtain ⟨φ₁, hφ₁, hq₁⟩ :=
    ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two
      N' hpN' hε F m G hfn
  have hφφ : φ₁ = φ := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F)
    rw [hq₁, ModularCurve.qexpOfWeight, zpow_natCast, hG]
  rw [← hφφ]
  exact hφ₁

end S_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two (solution)
