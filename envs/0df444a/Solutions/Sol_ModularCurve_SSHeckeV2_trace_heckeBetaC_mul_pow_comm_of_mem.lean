-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e98d906b-c4e1-56f0-960b-427482d8c046

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
import Theorems.Thm_ModPForms_heckePS_heckePS_comm
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

namespace TLCommE4

theorem thetaJ_ne_zero (K : Type) [Field K] : thetaJ K ≠ 0 := by
  rw [thetaJ, thetaL_apply]
  refine mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero) ?_
  intro h
  have hc : (LaurentSeries.derivative K (jqModC K)).coeff (-2) = -1 := by
    rw [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff]
    rw [show (-2 : ℤ) + ((1 : ℕ) : ℤ) = -1 by norm_num, coeff_jqModC_neg_one, Ring.choose_one_right]
    simp
  rw [h] at hc
  simp at hc

theorem qexpOfWeight_injective (K : Type) [Field K] (m : ℤ) : Function.Injective (qexpOfWeight K m) := by
  intro a b h
  simp only [qexpOfWeight] at h
  exact mul_right_cancel₀ (zpow_ne_zero m (thetaJ_ne_zero K)) h

theorem coe_algebraMap_mul (K : Type) [Field K] (N : ℕ) [NeZero N] (c : K) (t : ↥(modularFunctionFieldC K N)) :
    ((algebraMap K ↥(modularFunctionFieldC K N) c * t : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = HahnSeries.C c * (t : LaurentSeries K) := by
  push_cast
  congr 1
  exact LaurentSeries.algebraMap_apply K c

end TLCommE4

open TLCommE4 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'N : ¬ ℓ' ∣ N) (hℓ'p : ℓ' ≠ p)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N))
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
     letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ')
     algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (heckeBetaC K N ℓ
              (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ' : K) ^ (m - 1)) *
                Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ')
                  (heckeBetaC K N ℓ' G * ModularCurve.heckeMultiplier N K ℓ' ^ m))
            * ModularCurve.heckeMultiplier N K ℓ ^ m)
     = algebraMap K ↥(modularFunctionFieldC K N) ((ℓ' : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ')
          (heckeBetaC K N ℓ'
              (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
                Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                  (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m))
            * ModularCurve.heckeMultiplier N K ℓ' ^ m)) := by
  letI iℓ := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  letI iℓ' := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ')

  set T : ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N) := fun X =>
    algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
      Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
        (heckeBetaC K N ℓ X * ModularCurve.heckeMultiplier N K ℓ ^ m) with hT
  set T' : ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N) := fun X =>
    algebraMap K ↥(modularFunctionFieldC K N) ((ℓ' : K) ^ (m - 1)) *
      Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ')
        (heckeBetaC K N ℓ' X * ModularCurve.heckeMultiplier N K ℓ' ^ m) with hT'
  show T (T' G) = T' (T G)

  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hℓK : (ℓ : K) ≠ 0 := fun h => hℓp
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h)).symm
  have hℓ'K : (ℓ' : K) ≠ 0 := fun h => hℓ'p
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ'.Prime)).mp ((CharP.cast_eq_zero_iff K p ℓ').mp h)).symm

  haveI : NeZero (ℓ : K) := ⟨hℓK⟩
  haveI : NeZero (ℓ' : K) := ⟨hℓ'K⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ ℓ := HasEnoughRootsOfUnity.prim
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : K, IsPrimitiveRoot ζ' ℓ' := HasEnoughRootsOfUnity.prim
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hℓ'0 : ℓ' ≠ 0 := (Fact.out : ℓ'.Prime).ne_zero
  have hζu : IsUnit ζ := hζ.isUnit hℓ0
  have hζ'u : IsUnit ζ' := hζ'.isUnit hℓ'0
  have hζU : IsPrimitiveRoot ((hζu.unit : Kˣ) : K) ℓ := by simpa using hζ
  have hζ'U : IsPrimitiveRoot ((hζ'u.unit : Kˣ) : K) ℓ' := by simpa using hζ'

  have hD := ModularCurve.SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK
  have hD' := ModularCurve.SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ' hℓ'N hℓ'K

  have hGfn : IsModPFormFn K m (G : LaurentSeries K) :=
    (ModularCurve.mem_riemannRochSpace_weightDivisor_iff_isModPFormFn p hp5 N hpN K m G).mp hG
  obtain ⟨φ, -, hφ⟩ :=
    ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed p hp5 N hpN K m hm G hGfn

  have E1 := ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ' hN hℓ'N _ hζ'U m hm G φ hφ
    (ModularCurve.heckeMultiplier N K ℓ') hD'
  have E2 := ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ hN hℓN _ hζU m hm G φ hφ
    (ModularCurve.heckeMultiplier N K ℓ) hD
  rw [← coe_algebraMap_mul] at E1 E2
  change HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ' φ) = qexpOfWeight K (m : ℤ) ((T' G : ↥(modularFunctionFieldC K N)) : LaurentSeries K) at E1
  change HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ φ) = qexpOfWeight K (m : ℤ) ((T G : ↥(modularFunctionFieldC K N)) : LaurentSeries K) at E2

  have E12 := ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ hN hℓN _ hζU m hm (T' G) _ E1
    (ModularCurve.heckeMultiplier N K ℓ) hD
  have E21 := ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ' hN hℓ'N _ hζ'U m hm (T G) _ E2
    (ModularCurve.heckeMultiplier N K ℓ') hD'
  rw [← coe_algebraMap_mul] at E12 E21
  change HahnSeries.ofPowerSeries ℤ K _ = qexpOfWeight K (m : ℤ) ((T (T' G) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) at E12
  change HahnSeries.ofPowerSeries ℤ K _ = qexpOfWeight K (m : ℤ) ((T' (T G) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) at E21
  rw [ModPForms.heckePS_heckePS_comm K (2 * (m : ℤ)) ℓ ℓ' (Fact.out) (Fact.out) φ] at E12
  have := E12.symm.trans E21
  exact Subtype.ext (qexpOfWeight_injective K (m : ℤ) this)

end S_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem (solution)
