-- Prove2me | solution 1 for ModularCurve.XZeroP.le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/660e421c-42e9-5794-bef7-ebac059f8554

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_ModularUnit

import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_forall_minimalPrimes_le_of_mem_ssJSet_tensor_chartAlgFin_mul_of_not_dvd

import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

import Theorems.Thm_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField

import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

namespace SSBottomAsm

section S1
variable (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (L : Type) [Field L] [CharZero L] [Algebra A L]

theorem exists_ringHom_ratLocalizedAt (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ f : ↥(GaloisRep.ratLocalizedAt p) →+* A,
      (algebraMap A L).comp f = algebraMap ↥(GaloisRep.ratLocalizedAt p) L := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hp
  have hunit : ∀ y : (Ideal.span {(p : ℤ)}).primeCompl, IsUnit (algebraMap ℤ A y) := by
    intro y
    by_contra hy
    have hmem : algebraMap ℤ A y ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hy
    let I : Ideal ℤ := Ideal.comap (algebraMap ℤ A) (IsLocalRing.maximalIdeal A)
    have hI : I.IsPrime := Ideal.comap_isPrime _ _
    have hpI : (p : ℤ) ∈ I := by
      change algebraMap ℤ A (p : ℤ) ∈ IsLocalRing.maximalIdeal A
      simpa using hAp
    have hle : Ideal.span {(p : ℤ)} ≤ I := (Ideal.span_singleton_le_iff_mem _).mpr hpI
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal hP (by simpa using hp0)
    have hEq : Ideal.span {(p : ℤ)} = I := hmax.eq_of_le hI.ne_top hle
    have hyI : (y : ℤ) ∈ I := hmem
    rw [← hEq] at hyI
    exact y.2 hyI
  refine ⟨IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) hunit, ?_⟩
  apply IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl
  rw [RingHom.comp_assoc, IsLocalization.lift_comp]
  exact RingHom.ext_int _ _

end S1

theorem le_of_forall_minimalPrimes_span_le_comap_includeRight
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (p : R) (ϖ : A)
    (hsurj : Function.Surjective (algebraMap R (A ⧸ Ideal.span {ϖ})))
    (hker : RingHom.ker (algebraMap R (A ⧸ Ideal.span {ϖ})) = Ideal.span {p})
    (P : Ideal (A ⊗[R] B)) [P.IsPrime] (hϖP : ϖ ⊗ₜ[R] (1 : B) ∈ P)
    (hB : ∀ 𝔭' ∈ (Ideal.span {algebraMap R B p}).minimalPrimes, 𝔭' ≤ Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) P) :
    ∀ 𝔭 ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}).minimalPrimes, 𝔭 ≤ P := by
  classical

  have hpA : algebraMap R A p ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap, ← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self p
  have hIiRp : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (algebraMap R B p) ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hpA
    have : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (algebraMap R B p) = (c ⊗ₜ[R] (1 : B)) * (ϖ ⊗ₜ[R] (1 : B)) := by
      rw [Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.algebraMap_apply',
        Algebra.TensorProduct.algebraMap_apply, ← hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

  have hψsurj : ∀ x : A ⊗[R] B, ∃ b : B, x - (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
        obtain ⟨r, hr⟩ := hsurj (Ideal.Quotient.mk _ a)
        rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hr
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
        refine ⟨r • b, ?_⟩
        have hcalc : a ⊗ₜ[R] b - (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (r • b) = -((c ⊗ₜ[R] b) * (ϖ ⊗ₜ[R] (1 : B))) := by
          rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
            TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
            neg_sub]
        rw [hcalc]
        exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    | add x y hx hy =>
        obtain ⟨b₁, h₁⟩ := hx
        obtain ⟨b₂, h₂⟩ := hy
        refine ⟨b₁ + b₂, ?_⟩
        have : x + y - (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (b₁ + b₂) = (x - (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b₁) + (y - (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b₂) := by
          rw [map_add]; abel
        rw [this]
        exact Ideal.add_mem _ h₁ h₂

  have hχ : ∃ χ : A ⊗[R] B →+* B ⧸ (Ideal.span {algebraMap R B p}),
      (∀ b, χ ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b) = Ideal.Quotient.mk (Ideal.span {algebraMap R B p}) b) ∧ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ RingHom.ker χ := by
    let g : R →+* A ⧸ Ideal.span {ϖ} := algebraMap R (A ⧸ Ideal.span {ϖ})
    let e : R ⧸ RingHom.ker g ≃+* A ⧸ Ideal.span {ϖ} := RingHom.quotientKerEquivOfSurjective hsurj
    let h : R →+* B ⧸ (Ideal.span {algebraMap R B p}) := (Ideal.Quotient.mk (Ideal.span {algebraMap R B p})).comp (algebraMap R B)
    have hh : ∀ r ∈ RingHom.ker g, h r = 0 := by
      intro r hr
      have hr' : r ∈ Ideal.span {p} := hker ▸ hr
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr'
      show Ideal.Quotient.mk (Ideal.span {algebraMap R B p}) (algebraMap R B (c * p)) = 0
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    let θ : A →+* B ⧸ (Ideal.span {algebraMap R B p}) :=
      ((Ideal.Quotient.lift (RingHom.ker g) h hh).comp e.symm.toRingHom).comp (Ideal.Quotient.mk (Ideal.span {ϖ}))
    have hθ : ∀ r : R, θ (algebraMap R A r) = algebraMap R (B ⧸ (Ideal.span {algebraMap R B p})) r := by
      intro r
      show (Ideal.Quotient.lift (RingHom.ker g) h hh) (e.symm (Ideal.Quotient.mk _ (algebraMap R A r))) = _
      have he : e.symm (Ideal.Quotient.mk _ (algebraMap R A r)) = Ideal.Quotient.mk _ r := by
        rw [Ideal.Quotient.mk_algebraMap]
        exact RingHom.quotientKerEquivOfSurjective_symm_apply hsurj r
      rw [he, Ideal.Quotient.lift_mk]
      rfl
    have hθϖ : θ ϖ = 0 := by
      show (Ideal.Quotient.lift (RingHom.ker g) h hh) (e.symm (Ideal.Quotient.mk _ ϖ)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), map_zero, map_zero]
    let θₐ : A →ₐ[R] B ⧸ (Ideal.span {algebraMap R B p}) := ⟨θ, hθ⟩
    let χ : A ⊗[R] B →ₐ[R] B ⧸ (Ideal.span {algebraMap R B p}) :=
      Algebra.TensorProduct.lift θₐ (Ideal.Quotient.mkₐ R (Ideal.span {algebraMap R B p})) (fun _ _ => Commute.all _ _)
    refine ⟨χ.toRingHom, fun b => ?_, ?_⟩
    · show χ ((1 : A) ⊗ₜ[R] b) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      show χ (ϖ ⊗ₜ[R] (1 : B)) = 0
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hθϖ
  obtain ⟨χ, hχb, hIχ⟩ := hχ
  have hkerψ : ∀ b : B, (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) → b ∈ (Ideal.span {algebraMap R B p}) := by
    intro b hb
    have := hIχ hb
    rw [RingHom.mem_ker, hχb, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hIP : (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hϖP

  have hreflect : ∀ K K' : Ideal (A ⊗[R] B), (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ K → (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ K' →
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) K ≤ Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) K' → K ≤ K' := by
    intro K K' hIK hIK' hle x hx
    obtain ⟨b, hb⟩ := hψsurj x
    have hbK : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ K := by
      have := K.sub_mem hx (hIK hb)
      rwa [sub_sub_cancel] at this
    have hbK' : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ K' := Ideal.mem_comap.1 (hle (Ideal.mem_comap.2 hbK))
    have := K'.add_mem (hIK' hb) hbK'
    rwa [sub_add_cancel] at this

  intro 𝔭 h𝔭
  have h𝔭prime : 𝔭.IsPrime := h𝔭.1.1
  have hI𝔭 : (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ 𝔭 := h𝔭.1.2
  have hQ : Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) 𝔭 ∈ (Ideal.span {algebraMap R B p}).minimalPrimes := by
    refine ⟨⟨Ideal.comap_isPrime (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) 𝔭, ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
      exact hI𝔭 hIiRp
    · rintro Q' ⟨hQ'prime, hJQ'⟩ hQ'le
      let ψ : B →+* (A ⊗[R] B) ⧸ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) := (Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)})).comp ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) : B →+* A ⊗[R] B)
      have hψapply : ∀ b, ψ b = Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b) := fun b => rfl
      have hψs : Function.Surjective ψ := by
        intro z
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨b, hb⟩ := hψsurj x
        exact ⟨b, by rw [hψapply]; exact (Ideal.Quotient.eq.2 hb).symm⟩
      have hkerQ' : RingHom.ker ψ ≤ Q' := by
        intro b hb
        rw [RingHom.mem_ker, hψapply, Ideal.Quotient.eq_zero_iff_mem] at hb
        exact hJQ' (hkerψ b hb)
      haveI : (Q'.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψs hkerQ'
      let q : Ideal (A ⊗[R] B) := Ideal.comap (Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)})) (Q'.map ψ)
      have hqprime : q.IsPrime := Ideal.comap_isPrime _ _
      have hIq : (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ≤ q := by
        intro x hx
        show Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) x ∈ Q'.map ψ
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
        exact Ideal.zero_mem _
      have hq𝔭 : q ≤ 𝔭 := by
        intro x hx
        change Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) x ∈ Q'.map ψ at hx
        obtain ⟨b, hbQ', hbx⟩ := (Ideal.mem_map_iff_of_surjective ψ hψs).1 hx
        rw [hψapply] at hbx
        have hbx' : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b - x ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) := Ideal.Quotient.eq.1 hbx
        have hb𝔭 : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ 𝔭 := Ideal.mem_comap.1 (hQ'le hbQ')
        have := 𝔭.sub_mem hb𝔭 (hI𝔭 hbx')
        rwa [sub_sub_cancel] at this
      have h𝔭q : 𝔭 ≤ q := h𝔭.2 ⟨hqprime, hIq⟩ hq𝔭
      intro b hb
      have hbq : (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b ∈ q := h𝔭q (Ideal.mem_comap.1 hb)
      change Ideal.Quotient.mk (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}) ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b) ∈ Q'.map ψ at hbq
      obtain ⟨b', hb'Q', hb'b⟩ := (Ideal.mem_map_iff_of_surjective ψ hψs).1 hbq
      rw [hψapply] at hb'b
      have hbb' : b - b' ∈ Q' := by
        apply hkerQ'
        rw [RingHom.mem_ker, map_sub, sub_eq_zero, hψapply, hψapply]
        exact hb'b.symm
      have := Q'.add_mem hbb' hb'Q'
      rwa [sub_add_cancel] at this
  exact hreflect 𝔭 P hI𝔭 hIP (hB _ hQ)

section transport
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra A C]

theorem algEquiv_tmul_one (e : A ⊗[R] B ≃ₐ[A] C) (a : A) : e (a ⊗ₜ[R] (1 : B)) = algebraMap A C a := by
  rw [← e.commutes a, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem tmul_one_mem_comap (e : A ⊗[R] B ≃ₐ[A] C) (a : A) (y : Ideal C) (h : algebraMap A C a ∈ y) :
    a ⊗ₜ[R] (1 : B) ∈ Ideal.comap e.toRingEquiv.toRingHom y := by
  rw [Ideal.mem_comap]
  change e (a ⊗ₜ[R] (1 : B)) ∈ y
  rwa [algEquiv_tmul_one]

theorem natCast_mem_comap_includeRight (n : ℕ) (ϖ : A) (hn : (n : A) ∈ Ideal.span {ϖ})
    (P : Ideal (A ⊗[R] B)) (hP : ϖ ⊗ₜ[R] (1 : B) ∈ P) :
    ((n : ℕ) : B) ∈ Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) P := by
  rw [Ideal.mem_comap, map_natCast, Algebra.TensorProduct.natCast_def]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  rw [← hc, ← mul_one (1 : B), ← Algebra.TensorProduct.tmul_mul_tmul]
  exact P.mul_mem_left _ hP

theorem forall_minimalPrimes_span_le_of_ringEquiv {S T : Type} [CommRing S] [CommRing T] (e : S ≃+* T) (s : S)
    (y : Ideal T) (h : ∀ 𝔭 ∈ (Ideal.span {s}).minimalPrimes, 𝔭 ≤ Ideal.comap e.toRingHom y) :
    ∀ 𝔭 ∈ (Ideal.span {e s}).minimalPrimes, 𝔭 ≤ y := by
  intro 𝔭 h𝔭
  have hI : Ideal.span {e s} = Ideal.comap e.symm.toRingHom (Ideal.span {s}) := by
    change _ = Ideal.comap e.symm _
    rw [Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.comap_minimalPrimes_eq_of_surjective (f := e.symm.toRingHom) e.symm.surjective] at h𝔭
  obtain ⟨𝔮, h𝔮, rfl⟩ := h𝔭
  intro x hx
  have hx' : e.symm x ∈ 𝔮 := hx
  have := h 𝔮 h𝔮 hx'
  rw [Ideal.mem_comap] at this
  simpa using this

theorem forall_minimalPrimes_span_le_of_algEquiv (e : A ⊗[R] B ≃ₐ[A] C) (a : A) (y : Ideal C)
    (h : ∀ 𝔭 ∈ (Ideal.span {a ⊗ₜ[R] (1 : B)}).minimalPrimes, 𝔭 ≤ Ideal.comap e.toRingEquiv.toRingHom y) :
    ∀ 𝔭 ∈ (Ideal.span {algebraMap A C a}).minimalPrimes, 𝔭 ≤ y := by
  have h6 := forall_minimalPrimes_span_le_of_ringEquiv e.toRingEquiv (a ⊗ₜ[R] (1 : B)) y h
  have heq : e.toRingEquiv (a ⊗ₜ[R] (1 : B)) = algebraMap A C a := algEquiv_tmul_one e a
  rwa [heq] at h6

end transport

section transport2
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra A C]

theorem exists_sub_one_tmul_mem_span (ϖ : A)
    (hsurj : Function.Surjective (algebraMap R (A ⧸ Ideal.span {ϖ}))) (x : A ⊗[R] B) :
    ∃ b : B, x - (1 : A) ⊗ₜ[R] b ∈ Ideal.span {ϖ ⊗ₜ[R] (1 : B)} := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
      obtain ⟨r, hr⟩ := hsurj (Ideal.Quotient.mk _ a)
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hr
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
      refine ⟨r • b, ?_⟩
      have hcalc : a ⊗ₜ[R] b - (1 : A) ⊗ₜ[R] (r • b) = -((c ⊗ₜ[R] b) * (ϖ ⊗ₜ[R] (1 : B))) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc, TensorProduct.sub_tmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, neg_sub]
      rw [hcalc]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  | add x y hx hy =>
      obtain ⟨b₁, h₁⟩ := hx
      obtain ⟨b₂, h₂⟩ := hy
      refine ⟨b₁ + b₂, ?_⟩
      have : x + y - (1 : A) ⊗ₜ[R] (b₁ + b₂) = (x - (1 : A) ⊗ₜ[R] b₁) + (y - (1 : A) ⊗ₜ[R] b₂) := by
        rw [TensorProduct.tmul_add]; abel
      rw [this]
      exact Ideal.add_mem _ h₁ h₂

theorem exists_ringHom_ker_eq_comp_tmul {Ω : Type} [CommRing Ω] (ϖ : A)
    (hsurj : Function.Surjective (algebraMap R (A ⧸ Ideal.span {ϖ})))
    (e : A ⊗[R] B ≃ₐ[A] C) (y : Ideal C) (hϖy : algebraMap A C ϖ ∈ y)
    (φ : B →+* Ω)
    (hφ : RingHom.ker φ = Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
      (Ideal.comap e.toRingEquiv.toRingHom y)) :
    ∃ ψ : C →+* Ω, RingHom.ker ψ = y ∧ ∀ b : B, ψ (e ((1 : A) ⊗ₜ[R] b)) = φ b := by
  classical
  let y' : Ideal (A ⊗[R] B) := Ideal.comap e.toRingEquiv.toRingHom y
  have hmemy' : ∀ x : A ⊗[R] B, x ∈ y' ↔ e x ∈ y := fun x => Iff.rfl
  have hϖ' : ϖ ⊗ₜ[R] (1 : B) ∈ y' := by
    rw [hmemy', algEquiv_tmul_one]; exact hϖy
  have hIy' : Ideal.span {ϖ ⊗ₜ[R] (1 : B)} ≤ y' := (Ideal.span_singleton_le_iff_mem _).mpr hϖ'

  let θ : B →+* (A ⊗[R] B) ⧸ y' :=
    (Ideal.Quotient.mk y').comp (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have hθ : ∀ b, θ b = Ideal.Quotient.mk y' ((1 : A) ⊗ₜ[R] b) := fun b => rfl
  have hθsurj : Function.Surjective θ := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb⟩ := exists_sub_one_tmul_mem_span (B := B) ϖ hsurj x
    refine ⟨b, ?_⟩
    rw [hθ, eq_comm, Ideal.Quotient.eq]
    exact hIy' hb
  have hkerθ : RingHom.ker θ = RingHom.ker φ := by
    rw [hφ]
    ext b
    rw [RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem]
    exact Iff.rfl

  have Hφ : ∀ b : B, b ∈ RingHom.ker θ → φ b = 0 := fun b hb => by rwa [hkerθ, RingHom.mem_ker] at hb
  let φbar : (B ⧸ RingHom.ker θ) →+* Ω := Ideal.Quotient.lift (RingHom.ker θ) φ Hφ
  have hφbar_inj : Function.Injective φbar := (Ideal.injective_lift_iff Hφ).mpr hkerθ.symm
  let ε : (B ⧸ RingHom.ker θ) ≃+* (A ⊗[R] B) ⧸ y' := RingHom.quotientKerEquivOfSurjective hθsurj
  let Ψ : A ⊗[R] B →+* Ω := φbar.comp (ε.symm.toRingHom.comp (Ideal.Quotient.mk y'))
  have hΨ : ∀ x, Ψ x = φbar (ε.symm (Ideal.Quotient.mk y' x)) := fun x => rfl
  refine ⟨Ψ.comp e.symm.toRingEquiv.toRingHom, ?_, ?_⟩
  · ext x
    rw [RingHom.mem_ker, RingHom.comp_apply]
    change Ψ (e.symm x) = 0 ↔ x ∈ y
    rw [hΨ, ← map_zero φbar, hφbar_inj.eq_iff, ← map_zero ε.symm, ε.symm.injective.eq_iff,
      Ideal.Quotient.eq_zero_iff_mem, hmemy', e.apply_symm_apply]
  · intro b
    rw [RingHom.comp_apply]
    change Ψ (e.symm (e ((1 : A) ⊗ₜ[R] b))) = φ b
    rw [e.symm_apply_apply, hΨ, ← hθ, RingHom.quotientKerEquivOfSurjective_symm_apply]
    exact Ideal.Quotient.lift_mk _ _ _

end transport2

noncomputable def fibreChartFin (N p : ℕ) [NeZero N] [Fact p.Prime]
    (κ : Type) [CommRing κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ] :
    Spec (CommRingCat.of (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p))) ⟶
      pullback (igusaTo N p) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))) :=
  Spec.map (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin N p) κ).toRingEquiv.toCommRingCatIso.hom ≫
    (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin N p) κ).inv ≫
      (pullback.congrHom (IgusaScheme.ιFin_igusaTo N p) rfl).inv ≫
        (pullbackRightPullbackFstIso (igusaTo N p)
            (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))) (ιFin N p)).inv ≫
          pullback.snd (ιFin N p) (pullback.fst _ _)

scoped instance isOpenImmersion_fibreChartFin (N p : ℕ) [NeZero N] [Fact p.Prime]
    (κ : Type) [CommRing κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ] :
    IsOpenImmersion (fibreChartFin N p κ) := by
  unfold fibreChartFin; infer_instance

theorem isReduced_tensor_chartAlgFin_mul (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ] :
    IsReduced (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) := by
  haveI : AlgebraicGeometry.IsReduced
      (pullback (igusaTo (N * p) p) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ)))) :=
    ModularCurve.IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd N p hpN κ
  haveI := AlgebraicGeometry.isReduced_of_isOpenImmersion (fibreChartFin (N * p) p κ)
  exact (AlgebraicGeometry.affine_isReduced_iff _).mp this

theorem forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (y : Ideal ↥(chartAlgFin (N * p) p)) [y.IsPrime] (hyp : ((p : ℕ) : ↥(chartAlgFin (N * p) p)) ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin (N * p) p) →+* Ω), RingHom.ker φ = y → φ (jChartFin (N * p) p) ∈ ssJSet p Ω) :
    ∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes, 𝔭 ≤ y := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨A₀, hA₀⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
  haveI : CharP (IsLocalRing.ResidueField ↥A₀) p := ValuationSubring.charP_residueField_of_liesOverPrime p A₀ hA₀
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A₀) := ValuationSubring.isAlgClosed_residueField A₀
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime p A₀ hA₀
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField ↥A₀) := ((IsLocalRing.residue ↥A₀).comp ρ).toAlgebra

  obtain ⟨ι, w, hι, hw, σ, h0, -, -, -, -, -, -, -⟩ :=
    ModularCurve.IgusaScheme.exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd N p hpN A₀ hA₀ ρ hρ

  have hle : modularFunctionFieldFull p ≤ modularFunctionFieldFull (N * p) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left p N), rfl⟩
  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p) :=
    hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p)
  obtain ⟨hvA, -⟩ := ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N p hpN hmem
  let v : ↥(chartAlgFin (N * p) p) := ⟨⟨modularUnitSeries p, hmem⟩, hvA⟩
  have hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p := rfl

  haveI : IsReduced (IsLocalRing.ResidueField ↥A₀ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) := isReduced_tensor_chartAlgFin_mul N p hpN (IsLocalRing.ResidueField ↥A₀)

  refine ModularCurve.IgusaScheme.forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet_of_not_dvd
    N p hpN (IsLocalRing.ResidueField ↥A₀) ?_ y hyp hss
  intro 𝔮 _ hq
  exact ModularCurve.IgusaScheme.forall_minimalPrimes_le_of_mem_ssJSet_tensor_chartAlgFin_mul_of_not_dvd
    N p hpN (IsLocalRing.ResidueField ↥A₀) ι hι w hw (σ 0) h0 v hv 𝔮 hq

end SSBottomAsm
p2m_reactivate "P2MW.S_ModularCurve_XZeroP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul.SSBottomAsm"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₂) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j)) [y.IsPrime]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j) →+* Ω),
        RingHom.ker φ = y →
          φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₂) j) ∈ ModularCurve.ssJSet p Ω) :
    ∀ 𝔭 ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j) ϖ}).minimalPrimes,
      𝔭 ≤ y := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hp : p.Prime := Fact.out

  obtain ⟨f, hf⟩ := SSBottomAsm.exists_ringHom_ratLocalizedAt p A L hAp
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) A := f.toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L := IsScalarTower.of_algebraMap_eq' hf.symm
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L

  obtain ⟨e, he⟩ :=
    ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd
      M p hpM L K₂ hK₂ A hAp j hj

  let y' : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (M * p) p)) := Ideal.comap e.toRingEquiv.toRingHom y
  haveI hy' : y'.IsPrime := Ideal.comap_isPrime _ _
  have hϖ' : ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin (M * p) p)) ∈ y' :=
    SSBottomAsm.tmul_one_mem_comap e ϖ y hyϖ
  have hej : e ((1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (M * p) p) = TwoChartIntegralModel.jChartFin A (↥K₂) j := by
    apply Subtype.ext
    apply Subtype.ext
    rw [he]
    simp only [ModularCurve.IgusaScheme.coe_jChartFin, ModularCurve.IgusaScheme.coe_jFull,
      AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, hj]
  have hpϖA : (p : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp

  have hsurj : Function.Surjective (algebraMap ↥(GaloisRep.ratLocalizedAt p) (A ⧸ Ideal.span {ϖ})) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ :=
      IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp
        (IsLocalRing.residue A a)
    have hn' : IsLocalRing.residue A (n : A) = IsLocalRing.residue A a := by
      rw [map_intCast, ← hn, eq_intCast]
    have hna : (n : A) - a ∈ Ideal.span {ϖ} := by
      rw [← hϖ, ← Ideal.Quotient.eq]
      exact hn'
    refine ⟨n, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, map_intCast, Ideal.Quotient.eq]
    exact hna
  have hker : RingHom.ker (algebraMap ↥(GaloisRep.ratLocalizedAt p) (A ⧸ Ideal.span {ϖ})) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
    haveI := GaloisRep.ratLocalizedAt.isLocalRing hp
    have hne : Ideal.span {ϖ} ≠ ⊤ := by
      rw [← hϖ]; exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    haveI : Nontrivial (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.nontrivial_iff.mpr hne
    apply le_antisymm
    · rw [← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast,
        ← map_natCast (Ideal.Quotient.mk (Ideal.span {ϖ})) p, Ideal.Quotient.eq_zero_iff_mem]
      exact hpϖA
  have htrans : ∀ 𝔭 : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (M * p) p)),
      𝔭 ∈ (Ideal.span {ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin (M * p) p))}).minimalPrimes → 𝔭 ≤ y' := by

    intro 𝔭 h𝔭

    let yB : Ideal ↥(chartAlgFin (M * p) p) := Ideal.comap (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (M * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (M * p) p)) y'
    haveI : yB.IsPrime := Ideal.comap_isPrime _ _

    have hyBp : ((p : ℕ) : ↥(chartAlgFin (M * p) p)) ∈ yB :=
      SSBottomAsm.natCast_mem_comap_includeRight p ϖ hpϖA y' hϖ'
    have hssB : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin (M * p) p) →+* Ω), RingHom.ker φ = yB → φ (jChartFin (M * p) p) ∈ ssJSet p Ω := by

      intro Ω _ _ _ _ φ hφ
      obtain ⟨ψ, hkψ, hψ⟩ := SSBottomAsm.exists_ringHom_ker_eq_comp_tmul ϖ hsurj e y hyϖ φ hφ
      have := hss Ω ψ hkψ
      rwa [← hej, hψ] at this

    have h3 : ∀ 𝔭' ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (M * p) p))}).minimalPrimes, 𝔭' ≤ yB := by

      exact SSBottomAsm.forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet M p hpM yB hyBp hssB
    refine SSBottomAsm.le_of_forall_minimalPrimes_span_le_comap_includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := A) (B := ↥(chartAlgFin (M * p) p))
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ϖ hsurj hker y' hϖ' ?_ 𝔭 h𝔭
    simpa using h3

  exact SSBottomAsm.forall_minimalPrimes_span_le_of_algEquiv e ϖ y htrans

#print axioms solution

end S_ModularCurve_XZeroP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul (solution)
