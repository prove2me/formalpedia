-- Prove2me | solution 1 for ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7b7378c4-cc31-5142-91c5-8821edaa5a4c

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModPForms_mem_modPMod_of_map_mem_modPMod
import Theorems.Thm_ModularCurve_IsModPFormFn_coeffMap
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Theorems.Thm_ModPForms_one_mem_modPMod_zero
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed_of_charP_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "ModularCurve~coeffMap_mem_modularFunctionFieldC Polynomial"

namespace Ws12Katz3
namespace LiftZero

section Val
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_valuationSubring_of_isIntegral_subalgebra (V : ValuationSubring F) (A : Subalgebra K F)
    (hA : ∀ a ∈ A, a ∈ V) {z : F} (hz : IsIntegral A z) : z ∈ V := by

  let φ : A →+* V.toSubring :=
    { toFun := fun a => ⟨a, hA a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hp, hpz⟩ := hz
  have hz' : IsIntegral V.toSubring z := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpz
  haveI : IsIntegrallyClosedIn V.toSubring F := inferInstanceAs (IsIntegrallyClosedIn V F)
  obtain ⟨w, hw⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hz'
  rw [← hw]
  exact w.2

theorem mem_valuationSubring_of_pow_mem (V : ValuationSubring F) {y : F} {a : ℕ} (ha : a ≠ 0)
    (h : y ^ a ∈ V) : y ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' ha).mp h

theorem isIntegral_of_isIntegral_pow_adjoin_of_isIntegral_pow_adjoin_inv (x y : F) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : IsIntegral (Algebra.adjoin K ({x} : Set F)) (y ^ a))
    (h₂ : IsIntegral (Algebra.adjoin K ({x⁻¹} : Set F)) (y ^ b)) :
    IsIntegral K y := by
  by_contra hy
  have hyR : y ∉ (integralClosure K F).toSubring := fun h => hy ((mem_integralClosure_iff K F).mp h)
  haveI : IsIntegrallyClosedIn (integralClosure K F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure K F) F)
  obtain ⟨V, hRV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hyR
  have hKV : ∀ c : K, algebraMap K F c ∈ V := fun c =>
    hRV (show algebraMap K F c ∈ (integralClosure K F).toSubring from (integralClosure K F).algebraMap_mem c)

  let V' : Subalgebra K F :=
    { carrier := V
      mul_mem' := fun ha hb => V.mul_mem _ _ ha hb
      one_mem' := V.one_mem
      add_mem' := fun ha hb => V.add_mem _ _ ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := hKV }
  have hV' : ∀ s : F, s ∈ V → ∀ z ∈ Algebra.adjoin K ({s} : Set F), z ∈ V := by
    intro s hs z hz
    have hle : Algebra.adjoin K ({s} : Set F) ≤ V' :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
    exact hle hz
  apply hyV
  rcases V.mem_or_inv_mem x with hx | hx
  · exact mem_valuationSubring_of_pow_mem V ha
      (mem_valuationSubring_of_isIntegral_subalgebra V _ (hV' x hx) h₁)
  · exact mem_valuationSubring_of_pow_mem V hb
      (mem_valuationSubring_of_isIntegral_subalgebra V _ (hV' x⁻¹ hx) h₂)

end Val

section LS
variable {K : Type} [Field K]

theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem coeff_aeval (p : K[X]) (x : LaurentSeries K) (g : ℤ) :
    (aeval x p).coeff g = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i).coeff g := by
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_eq_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem order_eq_zero_of_isIntegral {x : LaurentSeries K} (hx : IsIntegral K x) (h0 : x ≠ 0) :
    x.order = 0 := by
  set p := minpoly K x with hp
  have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hx h0
  have hpx : aeval x p = 0 := minpoly.aeval K x
  have hmon : p.coeff p.natDegree = 1 := (minpoly.monic hx).coeff_natDegree
  rcases lt_trichotomy x.order 0 with hneg | h | hpos
  ·
    exfalso
    have key := congrArg (fun y : LaurentSeries K => y.coeff ((p.natDegree : ℤ) * x.order)) hpx
    try simp only at key
    rw [coeff_aeval, HahnSeries.coeff_zero, Finset.sum_eq_single p.natDegree] at key
    · rw [hmon, one_mul] at key
      have h2 : (x ^ p.natDegree).order = (p.natDegree : ℤ) * x.order := by
        rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact (HahnSeries.coeff_order_eq_zero.not.mpr) (pow_ne_zero _ h0) (h2 ▸ key)
    · intro i hi hne
      have hi' : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast hi') hneg
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · exact h
  ·
    exfalso
    have key := congrArg (fun y : LaurentSeries K => y.coeff 0) hpx
    try simp only at key
    rw [coeff_aeval, HahnSeries.coeff_zero, Finset.sum_eq_single 0] at key
    · rw [pow_zero, HahnSeries.coeff_one, if_pos rfl, mul_one] at key
      exact hp0 key
    · intro i _ hne
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hne) hpos
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem eq_C_of_isIntegral {x : LaurentSeries K} (hx : IsIntegral K x) : x = HahnSeries.C (x.coeff 0) := by
  set z := x - HahnSeries.C (x.coeff 0) with hz
  have hzint : IsIntegral K z := hx.sub (by rw [← algebraMap_eq_C]; exact isIntegral_algebraMap)
  have hz0 : z.coeff 0 = 0 := by
    rw [hz, HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]
  by_contra hne
  have hzne : z ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hord := order_eq_zero_of_isIntegral hzint hzne
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) hzne (hord ▸ hz0)

end LS

end Ws12Katz3.LiftZero

noncomputable section

namespace Ws12Katz3

section BaseChange

variable {K L : Type} [Field K] [Field L] (i : K →+* L) (N : ℕ) [NeZero N]

theorem coeffMap_mem_modularFunctionFieldC {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldC K N) :
    coeffMap i x ∈ modularFunctionFieldC L N := by

  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ {jqModC K, jqNModC K N}) at hx
  change coeffMap i x ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ {jqModC L, jqNModC L N})
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | hy
    · refine Subfield.subset_closure (Or.inl ⟨i c, ?_⟩)
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
    · refine Subfield.subset_closure (Or.inr ?_)
      rcases hy with rfl | rfl
      · left; exact (coeffMap_jqModC i).symm ▸ rfl
      · right; rw [Set.mem_singleton_iff] ; exact (coeffMap_jqNModC i N)
  | one => rw [map_one]; exact Subfield.one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem coeffMap_thetaJ : coeffMap i (thetaL K (jqModC K)) = thetaL L (jqModC L) := by
  have hK : thetaL K (jqModC K) = coeffMap (Int.castRingHom K)
      (HahnSeries.single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)) := by
    rw [← thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC]
  have hL : thetaL L (jqModC L) = coeffMap (Int.castRingHom L)
      (HahnSeries.single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)) := by
    rw [← thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC]
  rw [hK, hL, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) _

theorem coeffMap_qexpOfWeight (m : ℤ) (x : LaurentSeries K) :
    coeffMap i (qexpOfWeight K m x) = qexpOfWeight L m (coeffMap i x) := by
  simp only [qexpOfWeight, thetaJ, map_mul, map_zpow₀, coeffMap_thetaJ]

theorem exists_eq_ofPowerSeries_of_coeffMap_eq (hi : Function.Injective i) (x : LaurentSeries K) (φ : PowerSeries L)
    (h : coeffMap i x = HahnSeries.ofPowerSeries ℤ L φ) :
    ∃ ψ : PowerSeries K, HahnSeries.ofPowerSeries ℤ K ψ = x ∧ ψ.map i = φ := by
  refine ⟨PowerSeries.mk fun n => x.coeff n, ?_, ?_⟩
  · ext k
    rw [PowerSeries.coeff_coe]
    split_ifs with hk
    ·
      have := congrArg (fun y : LaurentSeries L => y.coeff k) h
      simp only [coeffMap_coeff, PowerSeries.coeff_coe, if_pos hk] at this
      exact (hi (by rw [this, map_zero])).symm
    · rw [PowerSeries.coeff_mk]
      congr 1; omega
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [← coeffMap_ofPowerSeries, ← h]
    congr 1
    ext k
    rw [PowerSeries.coeff_coe]
    split_ifs with hk
    · have := congrArg (fun y : LaurentSeries L => y.coeff k) h
      simp only [coeffMap_coeff, PowerSeries.coeff_coe, if_pos hk] at this
      exact (hi (by rw [this, map_zero])).symm
    · rw [PowerSeries.coeff_mk]; congr 1; omega

end BaseChange

open Ws12Katz3.LiftZero in

theorem weight_zero (N : ℕ) [NeZero N] (K : Type) [Field K]
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPFormFn K 0 (G : LaurentSeries K)) :
    ∃ φ : PowerSeries K, φ ∈ ModPForms.modPMod N (2 * ((0 : ℕ) : ℤ)) K ∧
      HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K ((0 : ℕ) : ℤ) (G : LaurentSeries K) := by
  obtain ⟨h₁, h₂⟩ := hG
  simp only [mul_zero, pow_zero, mul_one] at h₁ h₂
  have hint : IsIntegral K (G : LaurentSeries K) :=
    isIntegral_of_isIntegral_pow_adjoin_of_isIntegral_pow_adjoin_inv (jqModC K) _ (by norm_num)
      (by norm_num) h₁ h₂
  set c := (G : LaurentSeries K).coeff 0 with hc
  have hGc : (G : LaurentSeries K) = HahnSeries.C c := eq_C_of_isIntegral hint
  refine ⟨c • 1, ?_, ?_⟩
  · rw [show (2 * ((0 : ℕ) : ℤ) : ℤ) = 0 by norm_num]
    exact Submodule.smul_mem _ c (ModPForms.one_mem_modPMod_zero N K)
  · unfold qexpOfWeight
    rw [Nat.cast_zero, zpow_zero, mul_one, hGc, Algebra.smul_def, mul_one]
    simp

theorem main (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N) (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (K : Type) [Field K] [CharP K 3] (m : ℕ)
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    ∃ φ : PowerSeries K, φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K ∧
      HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K (m : ℤ) (G : LaurentSeries K) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact weight_zero N K G hG
  ·
    let Kb := AlgebraicClosure K
    let i : K →+* Kb := algebraMap K Kb
    haveI : CharP Kb 3 := charP_of_injective_algebraMap i.injective 3
    let G' : ↥(modularFunctionFieldC Kb N) := ⟨coeffMap i G, coeffMap_mem_modularFunctionFieldC i N G.2⟩
    have hG' : IsModPFormFn Kb m (G' : LaurentSeries Kb) := ModularCurve.IsModPFormFn.coeffMap i m _ hG

    obtain ⟨φb, hφb, hqb⟩ :=
      ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed_of_charP_three
        N hpN hε Kb m hm G' hG'

    have hq' : coeffMap i (qexpOfWeight K (m : ℤ) (G : LaurentSeries K)) = HahnSeries.ofPowerSeries ℤ Kb φb := by
      rw [coeffMap_qexpOfWeight, hqb]
    obtain ⟨ψ, hψx, hψφ⟩ := exists_eq_ofPowerSeries_of_coeffMap_eq i i.injective _ φb hq'
    refine ⟨ψ, ?_, hψx⟩
    exact ModPForms.mem_modPMod_of_map_mem_modPMod N (2 * (m : ℤ)) K Kb i ψ (hψφ ▸ hφb)

end Ws12Katz3

end

open ModPForms in
theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (G : ↥(ModularCurve.modularFunctionFieldC F N')) (hG : ModularCurve.IsModPFormFn F m (G : LaurentSeries F)) :
    ∃ φ : PowerSeries F, φ ∈ modPMod N' (2 * (m : ℤ)) F ∧
      HahnSeries.ofPowerSeries ℤ F φ = ModularCurve.qexpOfWeight F (m : ℤ) (G : LaurentSeries F) :=
  Ws12Katz3.main N' hpN' hε F m G hG

end S_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_three_of_exists_prime_dvd_mod_three_eq_two (solution)
