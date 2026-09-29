-- Prove2me | solution 1 for ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5c45954c-0679-570a-bcfa-8b2f19a30b8e

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_of_isModPFormFn
import Theorems.Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent
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

open AlgebraicCurve ModularCurve

namespace DimDownC0

theorem one_le_cuspCount (N : ℕ) [NeZero N] : 1 ≤ cuspCount N := by
  rw [cuspCount]
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 (NeZero.ne N)
  have := Finset.single_le_sum (f := fun d => Nat.totient (Nat.gcd d (N / d))) (fun _ _ => Nat.zero_le _) h1
  simpa using this

theorem two_le_cuspCount {N : ℕ} (hN : 2 ≤ N) : 2 ≤ cuspCount N := by
  rw [cuspCount]
  have hN0 : N ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 hN0
  have hNN : N ∈ N.divisors := Nat.mem_divisors_self N hN0
  have hne : (1 : ℕ) ≠ N := by omega
  have hsub : ({1, N} : Finset ℕ) ⊆ N.divisors := by
    intro d hd; rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl; exacts [h1, hNN]
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => Nat.zero_le (Nat.totient (Nat.gcd d (N / d))))
  rw [Finset.sum_pair hne] at this
  simp only [Nat.gcd_one_left, Nat.totient_one, Nat.div_self (Nat.pos_of_ne_zero hN0), Nat.gcd_one_right] at this
  omega

theorem nuTwo_one : nuTwo 1 = 1 := by
  rw [nuTwo]
  haveI : Unique {x : ZMod 1 // x ^ 2 + 1 = 0} :=
    { default := ⟨0, Subsingleton.elim _ _⟩, uniq := fun _ => Subsingleton.elim _ _ }
  exact Nat.card_unique

theorem nuThree_one : nuThree 1 = 1 := by
  rw [nuThree]
  haveI : Unique {x : ZMod 1 // x ^ 2 + x + 1 = 0} :=
    { default := ⟨0, Subsingleton.elim _ _⟩, uniq := fun _ => Subsingleton.elim _ _ }
  exact Nat.card_unique

theorem genusFormula_one : genusFormula 1 = 0 := by
  rw [genusFormula, dedekindPsi_one, nuTwo_one, nuThree_one, cuspCount_one]; norm_num

theorem nonspecial (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) {g : ℚ} (hg : g = genusFormula N) (hg0 : 0 ≤ g) :
    0 ≤ ((m : ℚ) - 1) * (2 * g - 2) + (m : ℚ) * (cuspCount N : ℚ) - 1
      + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) := by
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have h2 : (0 : ℚ) ≤ ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ) := by positivity
  have h3 : (0 : ℚ) ≤ ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) := by positivity
  rcases Nat.lt_or_ge N 2 with hN | hN
  ·
    have hN1 : N = 1 := by have := NeZero.ne N; omega
    subst hN1
    rw [genusFormula_one] at hg
    subst hg
    rw [nuTwo_one, nuThree_one, cuspCount_one]
    push_cast
    have key : (m : ℚ) - 1 ≤ ((m / 2 : ℕ) : ℚ) + ((2 * m / 3 : ℕ) : ℚ) := by
      have : m - 1 ≤ m / 2 + 2 * m / 3 := by omega
      have h' : ((m - 1 : ℕ) : ℚ) ≤ ((m / 2 + 2 * m / 3 : ℕ) : ℚ) := by exact_mod_cast this
      push_cast [Nat.cast_sub hm] at h'
      linarith
    nlinarith
  · have hc : (2 : ℚ) ≤ cuspCount N := by exact_mod_cast two_le_cuspCount hN
    nlinarith

end DimDownC0

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open DimDownC0 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K]
    (m : ℕ) (hm : 1 ≤ m) {ι : Type} [Fintype ι]
    (G : ι → ↥(modularFunctionFieldFullC K N)) (hG : ∀ i, IsModPFormFn K m (G i : LaurentSeries K))
    (hli : LinearIndependent K G) :
    (Fintype.card ι : ℚ) ≤ (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
      + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
      + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) := by
  classical
  have hram := ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP p hp5 N hpN K
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : (j : LaurentSeries K) = jqModC K := rfl

  have hpp : p.Prime := Fact.out
  have hcast : ∀ n : ℕ, (n : K) = 0 ↔ p ∣ n := fun n => CharP.cast_eq_zero_iff K p n
  have hN : (N : K) ≠ 0 := fun h => hpN ((hcast N).1 h)
  have h2 : (2 : K) ≠ 0 := fun h => by
    have := Nat.le_of_dvd (by norm_num) ((hcast 2).1 (by exact_mod_cast h)); omega
  have h3 : (3 : K) ≠ 0 := fun h => by
    have := Nat.le_of_dvd (by norm_num) ((hcast 3).1 (by exact_mod_cast h)); omega
  have h6N : ((6 * N : ℕ) : K) ≠ 0 := by
    push_cast
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h3) hN
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  haveI : IsCurveOver K ↥(modularFunctionFieldFullC K N) := isCurveOver_modularFunctionFieldFullC K N
  haveI : Algebra.EssFiniteType K ↥(modularFunctionFieldFullC K N) := essFiniteType_modularFunctionFieldFullC K N
  haveI : Nonempty (Place K ↥(modularFunctionFieldFullC K N)) := ⟨qInftyPlaceMod K (jqModC_mem_full K N)⟩

  have hj0 : j ≠ 0 := by
    intro h
    have : (j : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hjcoe] at this
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  have hjc : j - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 ≠ 0 := by
    intro h
    have h' : (j : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := by
      rw [sub_eq_zero] at h; rw [h]; rfl
    rw [hjcoe] at h'
    exact (transcendental_jqModC K) (h' ▸ isAlgebraic_algebraMap (1728 : K))

  obtain ⟨Dj, hDj, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) j hj0
  obtain ⟨Dc, hDc, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) (j - algebraMap K _ 1728) hjc
  let f : Place K ↥(modularFunctionFieldFullC K N) → ℤ := fun w =>
    (if 0 < w.ord j then (2 * (m : ℤ) * w.ord j) / 3 else 0)
      + (if 0 < w.ord (j - algebraMap K _ 1728) then ((m : ℤ) * w.ord (j - algebraMap K _ 1728)) / 2 else 0)
      + (if w.ord j < 0 then (m : ℤ) * w.ord j else 0)
  have hfsupp : ∀ w, f w ≠ 0 → w ∈ Dj.support ∪ Dc.support := by
    intro w hw
    rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff, hDj w, hDc w]
    by_contra h
    push_neg at h
    obtain ⟨h0, h1⟩ := h
    apply hw
    simp only [f, h0, h1, lt_irrefl, if_false, add_zero]
  let D : Divisor K ↥(modularFunctionFieldFullC K N) := Finsupp.onFinset (Dj.support ∪ Dc.support) f hfsupp
  have hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord j then (2 * (m : ℤ) * w.ord j) / 3 else 0)
        + (if 0 < w.ord (j - algebraMap K _ 1728) then ((m : ℤ) * w.ord (j - algebraMap K _ 1728)) / 2 else 0)
        + (if w.ord j < 0 then (m : ℤ) * w.ord j else 0) := fun w => Finsupp.onFinset_apply

  have hmem : ∀ i, G i ∈ riemannRochSpace D := fun i =>
    mem_riemannRochSpace_of_isModPFormFn K h1728 N m D hD (G i) (hG i)

  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K ↥(modularFunctionFieldFullC K N))) :=
    finiteDimensional_lSpace_zero K ↥(modularFunctionFieldFullC K N)
  haveI : FiniteDimensional K ↥(LSpace D) := finiteDimensional_lSpace D
  let G' : ι → ↥(LSpace D) := fun i => ⟨G i, hmem i⟩
  have hli' : LinearIndependent K G' :=
    LinearIndependent.of_comp (LSpace D).subtype (by exact hli)
  have hcard : Fintype.card ι ≤ ell D := hli'.fintype_card_le_finrank

  have hdegQ := degree_eq_of_forall_eq_weightFloor K N h6N m hram D hD
  have hgen := genusFF_modularFunctionFieldFullC_eq_genusFormula p hp5 N hpN K
  have hg0 : (0 : ℚ) ≤ genusFormula N := by rw [← hgen]; positivity

  have hns : 2 * (genusFF K ↥(modularFunctionFieldFullC K N) : ℤ) - 1 ≤ D.degree := by
    have hq : (2 * (genusFF K ↥(modularFunctionFieldFullC K N) : ℤ) - 1 : ℚ) ≤ (D.degree : ℚ) := by
      have := nonspecial N m hm rfl hg0
      push_cast
      rw [hgen, hdegQ]
      nlinarith
    exact_mod_cast hq

  have hRR := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC K N D hns
  have hRRQ : (ell D : ℚ) = (D.degree : ℚ) + 1 - (genusFF K ↥(modularFunctionFieldFullC K N) : ℚ) := by
    exact_mod_cast hRR
  have hcardQ : (Fintype.card ι : ℚ) ≤ (ell D : ℚ) := by exact_mod_cast hcard
  rw [hRRQ, hdegQ, hgen] at hcardQ
  nlinarith

end S_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent (solution)
