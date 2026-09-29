-- Prove2me | solution 1 for ModularCurve.ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fb3cb065-8c6e-5311-bf81-8a7fc20a0c0f

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor
import Theorems.Thm_ModularCurve_card_fibres_jqModC_modularFunctionFieldFullC_eq
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

namespace EllCusp

noncomputable def dCusp (N m : ℕ) : ℚ :=
  (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
    + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)
    + (if m = 1 then 1 else 0)

theorem one_le_cuspCount (N : ℕ) [NeZero N] : 1 ≤ cuspCount N := by
  unfold cuspCount
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 (NeZero.ne N)
  calc 1 = Nat.totient (Nat.gcd 1 (N / 1)) := by simp
    _ ≤ ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) :=
        Finset.single_le_sum (f := fun d => Nat.totient (Nat.gcd d (N / d))) (fun _ _ => Nat.zero_le _) h1

theorem nonspecial_arith (m : ℕ) (hm : 2 ≤ m) (g ν₂ ν₃ νi ψ : ℕ) (hψ : 1 ≤ ψ) (hνi : 1 ≤ νi)
    (hg : (g : ℚ) = 1 + (ψ : ℚ) / 12 - (ν₂ : ℚ) / 4 - (ν₃ : ℚ) / 3 - (νi : ℚ) / 2) :
    2 * (g : ℤ) - 1 ≤ (m : ℤ) * (2 * g - 2) + ((m / 2 : ℕ) : ℤ) * ν₂ + ((2 * m / 3 : ℕ) : ℤ) * ν₃ + ((m : ℤ) - 1) * νi := by

  have h12 : 12 * (g : ℤ) = 12 + ψ - 3 * ν₂ - 4 * ν₃ - 6 * νi := by
    have : (12 * (g : ℚ)) = 12 + ψ - 3 * ν₂ - 4 * ν₃ - 6 * νi := by rw [hg]; ring
    exact_mod_cast this
  have hA2 : 2 * ((m / 2 : ℕ) : ℤ) ≥ (m : ℤ) - 1 := by omega
  have hA3 : 3 * ((2 * m / 3 : ℕ) : ℤ) ≥ 2 * (m : ℤ) - 2 := by omega
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    subst hg0
    have h13 : 13 ≤ 3 * (ν₂ : ℤ) + 4 * ν₃ + 6 * νi := by omega

    rcases Nat.lt_or_ge m 7 with hsmall | hlarge
    · rcases (by omega : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with rfl | rfl | rfl | rfl | rfl
      all_goals (norm_num; omega)
    · have h2' : ((m / 2 : ℕ) : ℤ) * ν₂ * 2 ≥ ((m : ℤ) - 1) * ν₂ := by nlinarith
      have h3' : ((2 * m / 3 : ℕ) : ℤ) * ν₃ * 3 ≥ (2 * (m : ℤ) - 2) * ν₃ := by nlinarith
      nlinarith
  ·
    have h0 : 0 ≤ ((m / 2 : ℕ) : ℤ) * ν₂ := by positivity
    have h1 : 0 ≤ ((2 * m / 3 : ℕ) : ℤ) * ν₃ := by positivity
    have h2 : ((m : ℤ) - 1) * 1 ≤ ((m : ℤ) - 1) * νi := by
      apply mul_le_mul_of_nonneg_left <;> omega
    nlinarith

section Full

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (K : Type) [Field K] [CharP K p] [IsAlgClosed K]

include hp5 hpN in
theorem six_mul_ne_zero : ((6 * N : ℕ) : K) ≠ 0 := by
  intro h
  have h' := (CharP.cast_eq_zero_iff K p (6 * N)).1 h
  have hpr : p.Prime := Fact.out
  rcases (Nat.Prime.dvd_mul hpr).1 h' with h6 | hN
  · have : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases p
    · norm_num at h6
    · norm_num at hpr
  · exact hpN hN

noncomputable def J : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in
theorem J_ne_zero : J N K ≠ 0 := by
  intro h
  have : (jqModC K : LaurentSeries K) = 0 := by
    have := congrArg (fun z : ↥(modularFunctionFieldFullC K N) => (z : LaurentSeries K)) h
    exact this
  exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in
theorem J_sub_ne_zero : J N K - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 ≠ 0 := by
  intro h
  have h' : (jqModC K : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := by
    rw [sub_eq_zero] at h
    have := congrArg (fun z : ↥(modularFunctionFieldFullC K N) => (z : LaurentSeries K)) h
    exact this
  exact (transcendental_jqModC K) (h' ▸ isAlgebraic_algebraMap (1728 : K))

noncomputable def ind (T : Finset (Place K ↥(modularFunctionFieldFullC K N))) : Divisor K ↥(modularFunctionFieldFullC K N) :=
  ∑ w ∈ T, Finsupp.single w 1

open scoped Classical in
omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in
theorem ind_apply (T : Finset (Place K ↥(modularFunctionFieldFullC K N))) (v : Place K ↥(modularFunctionFieldFullC K N)) :
    ind N K T v = if v ∈ T then 1 else 0 := by
  classical
  unfold ind
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

omit [Fact p.Prime] [CharP K p] in
theorem degree_ind (T : Finset (Place K ↥(modularFunctionFieldFullC K N))) : (ind N K T).degree = T.card := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI := isCurveOver_modularFunctionFieldFullC K N
  unfold ind
  rw [map_sum]
  simp only [Divisor.degree_single, one_mul, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one]
  rw [Finset.sum_const]; simp

include hp5 hpN in
set_option maxHeartbeats 6400000 in

theorem main_full (m : ℕ) (hm : 1 ≤ m) (E : Divisor K ↥(modularFunctionFieldFullC K N))
    (hE : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      E w = ((if 0 < w.ord (J N K) then (2 * (m : ℤ) * w.ord (J N K)) / 3 else 0)
              + (if 0 < w.ord (J N K - algebraMap K _ 1728) then ((m : ℤ) * w.ord (J N K - algebraMap K _ 1728)) / 2 else 0)
              + (if w.ord (J N K) < 0 then (m : ℤ) * w.ord (J N K) else 0))
            - (if w.ord (J N K) < 0 then 1 else 0)) :
    (ell E : ℚ) ≤ dCusp N m := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI hco := isCurveOver_modularFunctionFieldFullC K N
  have h6N := six_mul_ne_zero p hp5 N hpN K

  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) (J N K) (J_ne_zero N K)
  obtain ⟨Dc, hDc, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) _ (J_sub_ne_zero N K)
  set T := Dj.support.filter (fun w => Dj w < 0) with hTdef
  set S0 := Dj.support.filter (fun w => 0 < Dj w) with hS0def
  set S1 := Dc.support.filter (fun w => 0 < Dc w) with hS1def
  have hT : ∀ w, w ∈ T ↔ w.ord (J N K) < 0 := by
    intro w; rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hDj w]; omega
  have hS0 : ∀ w, w ∈ S0 ↔ 0 < w.ord (J N K) := by
    intro w; rw [hS0def, Finset.mem_filter, Finsupp.mem_support_iff, hDj w]; omega
  have hS1 : ∀ w, w ∈ S1 ↔ 0 < w.ord (J N K - algebraMap K _ 1728) := by
    intro w; rw [hS1def, Finset.mem_filter, Finsupp.mem_support_iff, hDc w]; omega
  obtain ⟨-, -, hTcard⟩ := card_fibres_jqModC_modularFunctionFieldFullC_eq K N h6N S0 S1 T hS0 hS1 hT

  set D : Divisor K ↥(modularFunctionFieldFullC K N) := E + ind N K T with hDdef
  have hD : ∀ w, D w = ((if 0 < w.ord (J N K) then (2 * (m : ℤ) * w.ord (J N K)) / 3 else 0)
              + (if 0 < w.ord (J N K - algebraMap K _ 1728) then ((m : ℤ) * w.ord (J N K - algebraMap K _ 1728)) / 2 else 0)
              + (if w.ord (J N K) < 0 then (m : ℤ) * w.ord (J N K) else 0)) := by
    intro w
    rw [hDdef, Finsupp.add_apply, hE w, ind_apply,
      show (if w ∈ T then (1 : ℤ) else 0) = (if w.ord (J N K) < 0 then 1 else 0) from by simp only [hT w]]
    ring
  have hram := ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP p hp5 N hpN K
  have hdegD := degree_eq_of_forall_eq_weightFloor K N h6N m hram D hD
  have hdegE : (E.degree : ℚ) = (D.degree : ℚ) - cuspCount N := by
    have : D.degree = E.degree + (ind N K T).degree := by rw [hDdef, map_add]
    rw [this, degree_ind, hTcard]; push_cast; ring

  set g := genusFF K ↥(modularFunctionFieldFullC K N) with hgdef
  have hg : (g : ℚ) = genusFormula N := genusFF_modularFunctionFieldFullC_eq_genusFormula p hp5 N hpN K
  have hgf : genusFormula N = 1 + (dedekindPsi N : ℚ) / 12 - (nuTwo N : ℚ) / 4 - (nuThree N : ℚ) / 3 - (cuspCount N : ℚ) / 2 := rfl
  have hψ : 1 ≤ dedekindPsi N := dedekindPsi_pos N (NeZero.ne N)
  have hνi := one_le_cuspCount N

  have hdegE' : (E.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + ((m : ℚ) - 1) * (cuspCount N : ℚ) := by
    rw [hdegE, hdegD]; ring
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    have hm1' : m = 1 := by omega
    subst hm1'
    have hdeg1 : (E.degree : ℚ) = 2 * g - 2 := by rw [hdegE', ← hg]; push_cast; ring
    have hdeg1z : E.degree = 2 * (g : ℤ) - 2 := by exact_mod_cast hdeg1
    have hRHS : dCusp N 1 = g := by rw [hg]; unfold dCusp; norm_num
    rw [hRHS]
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    ·
      have : ell E = 0 := ell_eq_zero_of_degree_neg (by rw [hdeg1z, hg0]; norm_num)
      simp [this, hg0]
    ·
      have hTne : T.Nonempty := by
        rw [← Finset.card_pos, hTcard]; exact hνi
      obtain ⟨P, hP⟩ := hTne
      set E' := E + Finsupp.single P 1 with hE'def
      have hdegP : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
      have hdegE'z : E'.degree = 2 * (g : ℤ) - 1 := by
        rw [hE'def, map_add, Divisor.degree_single, hdegP, hdeg1z]; push_cast; ring
      have hRR := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC K N E' (by rw [hdegE'z, ← hgdef])
      rw [← hgdef, hdegE'z] at hRR
      have hellE' : (ell E' : ℤ) = g := by rw [hRR]; ring
      have hle : riemannRochSpace E ≤ riemannRochSpace E' := by
        intro f hf
        rw [mem_riemannRochSpace_iff] at hf ⊢
        intro v
        rcases hf v with h0 | h
        · exact Or.inl h0
        · right
          refine le_trans ?_ h
          rw [hE'def, Finsupp.add_apply, Finsupp.single_apply]
          split_ifs <;> omega
      have hfin : Module.Finite K (riemannRochSpace E') := by
        apply Module.finite_of_finrank_pos
        have : (Module.finrank K (riemannRochSpace E') : ℤ) = g := hellE'
        omega
      have hmono := Submodule.finrank_mono hle
      have : (ell E : ℤ) ≤ ell E' := by exact_mod_cast hmono
      have : (ell E : ℤ) ≤ g := by rw [← hellE']; exact this
      exact_mod_cast this
  ·
    have harith := nonspecial_arith m hm2 g (nuTwo N) (nuThree N) (cuspCount N) (dedekindPsi N) hψ hνi (by rw [hg, hgf])
    have hdegEz : (E.degree : ℤ) = (m : ℤ) * (2 * (g : ℤ) - 2) + ((m / 2 : ℕ) : ℤ) * (nuTwo N : ℤ) + ((2 * m / 3 : ℕ) : ℤ) * (nuThree N : ℤ)
        + ((m : ℤ) - 1) * (cuspCount N : ℤ) := by
      have h := hdegE'
      rw [← hg] at h
      have h' : ((E.degree : ℤ) : ℚ) = (((m : ℤ) * (2 * (g : ℤ) - 2) + ((m / 2 : ℕ) : ℤ) * (nuTwo N : ℤ) + ((2 * m / 3 : ℕ) : ℤ) * (nuThree N : ℤ)
          + ((m : ℤ) - 1) * (cuspCount N : ℤ) : ℤ) : ℚ) := by
        rw [h]; simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
      exact Int.cast_injective h'
    have hRR := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC K N E (by rw [hdegEz, ← hgdef]; exact harith)
    rw [← hgdef] at hRR
    unfold dCusp
    rw [if_neg (by omega : ¬ m = 1), add_zero]
    have : ((ell E : ℤ) : ℚ) = (E.degree : ℚ) + 1 - g := by rw [hRR]; push_cast; ring
    rw [show (ell E : ℚ) = ((ell E : ℤ) : ℚ) by push_cast; rfl, this, hdegE', ← hg]
    ring_nf
    rfl

end Full

theorem main_of_eq (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (m : ℕ) (hm : 1 ≤ m)
    (Ef : IntermediateField K (LaurentSeries K)) (hEq : modularFunctionFieldFullC K N = Ef) (hj : jqModC K ∈ Ef)
    (E : Divisor K ↥Ef)
    (hE : ∀ w : Place K ↥Ef,
      E w = ((if 0 < w.ord (⟨jqModC K, hj⟩ : ↥Ef) then (2 * (m : ℤ) * w.ord (⟨jqModC K, hj⟩ : ↥Ef)) / 3 else 0)
              + (if 0 < w.ord ((⟨jqModC K, hj⟩ : ↥Ef) - algebraMap K _ 1728) then ((m : ℤ) * w.ord ((⟨jqModC K, hj⟩ : ↥Ef) - algebraMap K _ 1728)) / 2 else 0)
              + (if w.ord (⟨jqModC K, hj⟩ : ↥Ef) < 0 then (m : ℤ) * w.ord (⟨jqModC K, hj⟩ : ↥Ef) else 0))
            - (if w.ord (⟨jqModC K, hj⟩ : ↥Ef) < 0 then 1 else 0)) :
    (ell E : ℚ) ≤ dCusp N m := by
  subst hEq
  exact main_full p hp5 N hpN K m hm E hE

end EllCusp

open EllCusp in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (m : ℕ) (hm : 1 ≤ m)
    (E : Divisor K ↥(modularFunctionFieldC K N))
    (hE : ∀ w : Place K ↥(modularFunctionFieldC K N),
      E w = ModularCurve.weightFloor K N m w - (if w.ord (jGeomGen K N) < 0 then 1 else 0)) :
    (ell E : ℚ) ≤ (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)
        + (if m = 1 then 1 else 0) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := main_of_eq p hp5 N hpN K m hm _ (modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K p N hpN).symm
    (jqModC_mem K N) E (fun w => by rw [hE w]; rfl)
  exact h

end S_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
end P2MW
export P2MW.S_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub (solution)
