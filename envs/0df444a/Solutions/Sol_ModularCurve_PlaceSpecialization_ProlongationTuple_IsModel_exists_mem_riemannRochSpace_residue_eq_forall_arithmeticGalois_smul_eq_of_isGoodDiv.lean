-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0b3ee5cd-f6ac-53d0-ae38-e912febf3706

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
import Theorems.Thm_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq
import Theorems.Thm_ModularCurve_exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional_mul
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace ResiduePairLift
namespace Inertia

open IsLocalRing

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem natCast_mem_maximalIdeal {p : ℕ} (hA : A.LiesOverPrime p) :
    ((p : ℕ) : A) ∈ maximalIdeal A := by
  have h : A.valuation (((p : ℕ) : A) : AlgebraicClosure ℚ) < 1 := by
    have h' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.mem_nonunits_iff] at h'
    simpa using h'
  exact (A.valuation_lt_one_iff _).mpr h

private theorem isUnit_natCast {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : A) := by
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn).symm
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
  have h1 : (u : A) * ((n : ℕ) : A) + (v : A) * ((p : ℕ) : A) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) huv
    push_cast at this
    exact this
  have hmem : (v : A) * ((p : ℕ) : A) ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_left _ (natCast_mem_maximalIdeal A hA)
  have hunit : IsUnit ((u : A) * ((n : ℕ) : A)) := by
    have e : (u : A) * ((n : ℕ) : A) = 1 - (v : A) * ((p : ℕ) : A) := by
      rw [← h1]; ring
    rw [e]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hmem
  exact isUnit_of_mul_isUnit_right hunit

private theorem eq_one_of_pow_eq_one_of_residue_eq_one {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) {u : A} (hu : u ^ n = 1) (hres : residue A u = 1) : u = 1 := by
  have hgeom : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  have hsum : residue A (∑ i ∈ Finset.range n, u ^ i) = residue A ((n : ℕ) : A) := by
    rw [map_sum, map_natCast]
    simp [map_pow, hres]
  have hunit : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range n, u ^ i) ∈ maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : residue A (∑ i ∈ Finset.range n, u ^ i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [hsum] at h0
    have hn' : ((n : ℕ) : A) ∈ maximalIdeal A := (Ideal.Quotient.eq_zero_iff_mem).mp h0
    exact ((IsLocalRing.mem_maximalIdeal _).mp hn') (isUnit_natCast A hp hA hn)
  have := (hunit.mul_right_eq_zero).mp hgeom
  exact sub_eq_zero.mp this

private theorem eq_of_pow_eq_one_of_residue_eq {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) {a b : A} (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hres : residue A a = residue A b) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0

  have hu : (a * b ^ m) ^ (m + 1) = 1 := by
    rw [mul_pow, ha, one_mul, ← pow_mul, mul_comm m (m + 1), pow_mul, hb, one_pow]
  have hures : residue A (a * b ^ m) = 1 := by
    rw [map_mul, map_pow, hres, ← map_pow, ← map_mul, ← pow_succ', hb, map_one]
  have h1 : a * b ^ m = 1 := eq_one_of_pow_eq_one_of_residue_eq_one A hp hA hn hu hures
  calc a = a * b ^ m * b := by rw [mul_assoc, ← pow_succ, hb, mul_one]
    _ = b := by rw [h1, one_mul]

private theorem mem_of_pow_eq_one {n : ℕ} (hn0 : n ≠ 0) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    ζ ∈ A := by
  apply A.mem_of_valuation_le_one
  have h : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
  by_contra hlt
  push Not at hlt
  have h2 : 1 < A.valuation ζ ^ n := one_lt_pow₀ hlt hn0
  rw [h] at h2
  exact lt_irrefl _ h2

private theorem exists_decomposition_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    ∃ g : A.decompositionSubgroup ℚ, (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ ∧
      ∀ y : ResidueField A, g • y = y := by
  unfold ValuationSubring.inertiaSubgroupIn at hσ
  rw [Subgroup.mem_map] at hσ
  obtain ⟨g, hgI, hgσ⟩ := hσ
  refine ⟨g, hgσ, fun y => ?_⟩
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (ResidueField A) g = 1 :=
    (MonoidHom.mem_ker).mp hgI
  have h2 := congrArg (fun e : RingAut (ResidueField A) => e y) h1
  simpa [MulSemiringAction.toRingAut_apply] using h2

private theorem forall_inertia_apply_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ ζ = ζ := by
  intro σ hσ
  obtain ⟨g, rfl, hfix⟩ := exists_decomposition_of_mem_inertiaSubgroupIn A hσ
  set a : A := ⟨ζ, mem_of_pow_eq_one A hn0 hζ⟩ with ha_def
  have ha : a ^ n = 1 := by
    ext; simp [ha_def, hζ]
  have hb : (g • a) ^ n = 1 := by
    rw [← smul_pow', ha, smul_one]
  have hres : residue A (g • a) = residue A a := by
    rw [ResidueField.residue_smul, hfix]
  have hab : g • a = a := eq_of_pow_eq_one_of_residue_eq A hp hA hn hb ha hres
  have hcoe : ((g • a : A) : AlgebraicClosure ℚ) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := rfl
  rw [← hcoe, hab]

private theorem exists_residue_eq_and_forall_inertia_apply_eq {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (x : ResidueField A) :
    ∃ a : A, residue A a = x ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = a := by
  classical
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx], fun σ _ => by simp⟩

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A hA
  obtain ⟨m, hpm, hm0, hxm⟩ : ∃ m : ℕ, ¬ p ∣ m ∧ m ≠ 0 ∧ x ^ m = 1 := by
    set y : AlgebraicClosure (ZMod p) := e x with hy
    have hy0 : y ≠ 0 := by
      intro h; apply hx
      simpa [hy] using (e.injective (h.trans (map_zero e).symm))
    have hyint : IsIntegral (ZMod p) y := (Algebra.IsIntegral.isIntegral (R := ZMod p) y)
    haveI : FiniteDimensional (ZMod p) (IntermediateField.adjoin (ZMod p) ({y} : Set (AlgebraicClosure (ZMod p)))) :=
      IntermediateField.adjoin.finiteDimensional hyint
    set F := IntermediateField.adjoin (ZMod p) ({y} : Set (AlgebraicClosure (ZMod p))) with hF
    haveI : Finite F := Module.finite_of_finite (ZMod p)
    letI : Fintype F := Fintype.ofFinite F
    have hyF : y ∈ F := IntermediateField.subset_adjoin _ _ (Set.mem_singleton y)
    set z : F := ⟨y, hyF⟩ with hz
    have hz0 : z ≠ 0 := by
      intro h; apply hy0; simpa [hz] using congrArg (fun w : F => (w : AlgebraicClosure (ZMod p))) h
    have hzpow : z ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one z hz0
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Fintype.card F = p ^ k := by
      haveI : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
      obtain ⟨k, hk⟩ := FiniteField.card F p
      exact ⟨k, hk.2⟩
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    refine ⟨Fintype.card F - 1, ?_, ?_, ?_⟩
    ·
      intro hdvd
      have hk0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk; omega
      have hpk : p ∣ p ^ k := dvd_pow_self p hk0
      rw [hk] at hdvd
      have hpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
      have hpk' : p ∣ (p ^ k - 1) + 1 := by rwa [Nat.sub_add_cancel hpos]
      have : p ∣ 1 := (Nat.dvd_add_right hdvd).mp hpk'
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · omega
    ·
      have hy' : y ^ (Fintype.card F - 1) = 1 := by
        have := congrArg (fun w : F => (w : AlgebraicClosure (ZMod p))) hzpow
        simpa [hz] using this
      apply e.injective
      rw [map_pow, map_one]
      exact hy'

  have hm_ne : ((m : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hm0
  set S : Finset (AlgebraicClosure ℚ) := (Polynomial.nthRoots m (1 : AlgebraicClosure ℚ)).toFinset with hS
  have hSmem : ∀ s ∈ S, s ^ m = 1 := by
    intro s hs
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0)] at hs
    exact hs
  have hScard : S.card = m := by
    have hnodup : (Polynomial.nthRoots m (1 : AlgebraicClosure ℚ)).Nodup := by
      unfold Polynomial.nthRoots
      exact Polynomial.nodup_roots
        ((Polynomial.separable_X_pow_sub_C (1 : AlgebraicClosure ℚ) hm_ne one_ne_zero))
    rw [hS, Multiset.toFinset_card_of_nodup hnodup]
    unfold Polynomial.nthRoots
    have hsplit := IsAlgClosed.splits (Polynomial.X ^ m - Polynomial.C (1 : AlgebraicClosure ℚ))
    rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit, Polynomial.natDegree_X_pow_sub_C]

  let lift : AlgebraicClosure ℚ → A := fun s =>
    if h : s ^ m = 1 then ⟨s, mem_of_pow_eq_one A hm0 h⟩ else 0
  have hlift : ∀ s ∈ S, ((lift s : A) : AlgebraicClosure ℚ) = s := by
    intro s hs; simp [lift, hSmem s hs]
  have hliftpow : ∀ s ∈ S, (lift s) ^ m = 1 := by
    intro s hs; ext; simp [hlift s hs, hSmem s hs]
  have hinj : Set.InjOn (fun s => residue A (lift s)) (S : Set (AlgebraicClosure ℚ)) := by
    intro s hs t ht hst
    have := eq_of_pow_eq_one_of_residue_eq A hp hA hpm (hliftpow s hs) (hliftpow t ht) hst
    have := congrArg (fun w : A => (w : AlgebraicClosure ℚ)) this
    simpa [hlift s hs, hlift t ht] using this
  set T : Finset (ResidueField A) := (Polynomial.nthRoots m (1 : ResidueField A)).toFinset with hT
  have himage : S.image (fun s => residue A (lift s)) ⊆ T := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0), ← map_pow,
      hliftpow s hs, map_one]
  have hTcard : T.card ≤ m := by
    rw [hT]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)
  have hScard' : (S.image (fun s => residue A (lift s))).card = m := by
    rw [Finset.card_image_of_injOn hinj, hScard]
  have hxT : x ∈ T := by
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0)]
    exact hxm
  have heq : S.image (fun s => residue A (lift s)) = T :=
    Finset.eq_of_subset_of_card_le himage (by rw [hScard']; exact hTcard)
  rw [← heq, Finset.mem_image] at hxT
  obtain ⟨s, hs, hsx⟩ := hxT
  refine ⟨lift s, hsx, fun σ hσ => ?_⟩
  rw [hlift s hs]
  exact forall_inertia_apply_eq_of_pow_eq_one A hp hA hpm hm0 (hSmem s hs) σ hσ

end ResiduePairLift.Inertia

namespace ResiduePairLift
namespace Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.ResiduePairLift.Eval.ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

p2m_export "ResiduePairLift.Eval" "ord_nonneg_of_mem"
private theorem _root_.ResiduePairLift.Eval.mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

p2m_export "ResiduePairLift.Eval" "mem_of_ord_nonneg"

private theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · simpa using Place.hasValue_algebraMap v (0 : K)
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

private theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 :=
  hasValue_zero_of_ord_pos v (Or.inl rfl)

private theorem hvAdd {v : Place K F} {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have e : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [e, map_add, hfr, hgr, map_add]

private theorem hvSmul {v : Place K F} {f : F} {a : K} (c : K) (hf : v.HasValue f a) :
    v.HasValue (c • f) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap v c).mul hf

private theorem hvSum {v : Place K F} {ι : Type*} (s : Finset ι) (f : ι → F) (b : ι → K)
    (h : ∀ j ∈ s, v.HasValue (f j) (b j)) :
    v.HasValue (∑ j ∈ s, f j) (∑ j ∈ s, b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact hvAdd (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (Finsupp.le_def.mp h v)).trans h0)

private theorem ne_zero_and_ord_add_eq_zero {D : Divisor K F} {f : F} {w : Place K F}
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    f ≠ 0 ∧ w.ord f + D w = 0 := by
  rw [mem_riemannRochSpace_iff] at hf hf'
  push Not at hf'
  obtain ⟨v, hf0, hv⟩ := hf'
  have hvw : v = w := by
    by_contra hne
    have h1 : (D - Finsupp.single w 1 : Divisor K F) v = D v := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero]
    rcases hf v with h | h
    · exact hf0 h
    · rw [h1] at hv
      exact absurd h (not_le.mpr hv)
  subst hvw
  refine ⟨hf0, ?_⟩
  rcases hf v with h | h
  · exact absurd h hf0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hv
    omega

private theorem exists_mem_riemannRochSpace_not_mem_of_finrank_lt {D D' : Divisor K F}
    [FiniteDimensional K ↥(riemannRochSpace D')]
    (h : Module.finrank K ↥(riemannRochSpace D') < Module.finrank K ↥(riemannRochSpace D)) :
    ∃ p ∈ riemannRochSpace D, p ∉ riemannRochSpace D' := by
  by_contra hcon
  push Not at hcon
  have hle : riemannRochSpace D ≤ riemannRochSpace D' := fun p hp => hcon p hp
  exact absurd (LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)) (not_le.mpr h)

private theorem twist_mul_mem {E : Divisor K F} {v : Place K F} {t p : F} (ht0 : t ≠ 0) (ht : v.ord t = E v)
    (hp : p ∈ riemannRochSpace E) : t * p ∈ v.toValuationSubring := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [mul_zero]; exact zero_mem _
  · apply mem_of_ord_nonneg v (mul_ne_zero ht0 hp0)
    rcases (mem_riemannRochSpace_iff.mp hp) v with h | h
    · exact absurd h hp0
    · rw [v.ord_mul ht0 hp0, ht]
      omega

private theorem exists_hasValue_twist_mul {E : Divisor K F} {v : Place K F} {t p : F}
    (hrat : Function.Surjective (algebraMap K v.ResidueField))
    (ht0 : t ≠ 0) (ht : v.ord t = E v) (hp : p ∈ riemannRochSpace E) :
    ∃ a : K, v.HasValue (t * p) a := by
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hrat (twist_mul_mem ht0 ht hp)
  exact ⟨a, ha⟩

section TwistedPairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def twistedPairs {ι : Type*} (E₁ E₂ : Divisor K F) (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F) (lam : ι → K) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c}
  zero_mem' := by
    refine ⟨zero_mem _, zero_mem _, fun i => ⟨0, ?_, ?_⟩⟩
    · rw [Prod.fst_zero, mul_zero, mul_zero]; exact hasValue_zero _
    · rw [Prod.snd_zero, mul_zero]; exact hasValue_zero _
  add_mem' := by
    rintro p q ⟨hp₁, hp₂, hp⟩ ⟨hq₁, hq₂, hq⟩
    refine ⟨add_mem hp₁ hq₁, add_mem hp₂ hq₂, fun i => ?_⟩
    obtain ⟨c, hc₁, hc₂⟩ := hp i
    obtain ⟨d, hd₁, hd₂⟩ := hq i
    refine ⟨c + d, ?_, ?_⟩
    · rw [Prod.fst_add, mul_add, mul_add]; exact hvAdd hc₁ hd₁
    · rw [Prod.snd_add, mul_add]; exact hvAdd hc₂ hd₂
  smul_mem' := by
    rintro a p ⟨hp₁, hp₂, hp⟩
    refine ⟨Submodule.smul_mem _ _ hp₁, Submodule.smul_mem _ _ hp₂, fun i => ?_⟩
    obtain ⟨c, hc₁, hc₂⟩ := hp i
    refine ⟨a * c, ?_, ?_⟩
    · rw [Prod.smul_fst, mul_smul_comm, mul_left_comm]; exact hvSmul a hc₁
    · rw [Prod.smul_snd, mul_smul_comm]; exact hvSmul a hc₂

private theorem mem_twistedPairs_iff {ι : Type*} (E₁ E₂ : Divisor K F) (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F)
    (lam : ι → K) (p : F × F) :
    p ∈ twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c :=
  Iff.rfl

end TwistedPairs

section Avoid

variable {k₀ K M : Type*} [Field k₀] [Field K] [AddCommGroup M] [Module K M]

private def coeffPreimage (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M) :
    Submodule k₀ (Fin n → k₀) where
  carrier := {μ | (∑ j, σ (μ j) • p j) ∈ H}
  zero_mem' := by
    show (∑ j, σ ((0 : Fin n → k₀) j) • p j) ∈ H
    simp only [Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]
    exact H.zero_mem
  add_mem' := by
    intro μ ν hμ hν
    show (∑ j, σ ((μ + ν) j) • p j) ∈ H
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact H.add_mem hμ hν
  smul_mem' := by
    intro c μ hμ
    show (∑ j, σ ((c • μ) j) • p j) ∈ H
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
    exact H.smul_mem _ hμ

private theorem mem_coeffPreimage_iff (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M)
    (μ : Fin n → k₀) : μ ∈ coeffPreimage σ p H ↔ (∑ j, σ (μ j) • p j) ∈ H :=
  Iff.rfl

private theorem exists_forall_sum_smul_notMem [Infinite k₀] (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M)
    {ι : Type*} [Finite ι] (H : ι → Submodule K M)
    (hH : ∀ i, ¬ (Submodule.span K (Set.range p) ≤ H i)) :
    ∃ μ : Fin n → k₀, ∀ i, (∑ j, σ (μ j) • p j) ∉ H i := by
  classical
  have hne : ∀ i, coeffPreimage σ p (H i) ≠ ⊤ := by
    intro i htop
    apply hH i
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (Pi.single j (1 : k₀) : Fin n → k₀) ∈ coeffPreimage σ p (H i) := by
      rw [htop]; exact Submodule.mem_top
    have hsum : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) = p j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, map_one, one_smul]
      · intro l _ hl
        rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hj' : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) ∈ H i := hj
    rw [hsum] at hj'
    exact hj'
  obtain ⟨μ, hμ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i => coeffPreimage σ p (H i)) hne
  exact ⟨μ, fun i h => hμ i h⟩

end Avoid

section Closed

variable [IsAlgClosed K] [IsCurveOver K F]

private theorem surjective_algebraMap_residueField (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Closed

end ResiduePairLift.Eval

namespace ResiduePairLift

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem Gauss.ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

private theorem Gauss.mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

private theorem Gauss.ord_neg_of_ord_sub_neg (v : Place K F) {f g : F} (hg : g ∈ v.toValuationSubring)
    (h : v.ord (f - g) < 0) : v.ord f < 0 := by
  rw [← Place.not_adicValuation_le_one_iff] at h ⊢
  intro hf
  apply h
  calc v.adicValuation (f - g) ≤ max (v.adicValuation f) (v.adicValuation g) := Valuation.map_sub _ _ _
    _ ≤ 1 := max_le hf (v.adicValuation_le_one_of_mem hg)

private theorem Gauss.ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (Place.hasValue_algebraMap v c).ord_eq_zero hc

private theorem Gauss.ord_smul_const (v : Place K F) {c : K} (hc : c ≠ 0) (f : F) : v.ord (c • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, Gauss.ord_algebraMap, zero_add]

private theorem Gauss.ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have h := v.ord_zpow f n
  rwa [zpow_natCast] at h

private theorem Gauss.ord_sub_pos_of_hasValue (v : Place K F) {g : F} {c : K} (h : v.HasValue g c)
    (hne : g ≠ algebraMap K F c) : 0 < v.ord (g - algebraMap K F c) := by
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem h.mem (v.algebraMap_mem' c)
  have hne0 : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hne
  have h0 : 0 ≤ v.ord (g - algebraMap K F c) := Gauss.ord_nonneg_of_mem v hne0 hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne0 heq.symm
    have e : (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring c := Subtype.ext rfl
    have hres : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hm⟩ = 0 := by
      rw [e, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

private theorem Gauss.exists_hasValue_of_deg_eq_one (v : Place K F) (hdeg : v.deg = 1) {g : F}
    (hg : g ∈ v.toValuationSubring) : ∃ a : K, v.HasValue g a := by
  have h1 : (1 : v.ResidueField) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective (algebraMap K v.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) h1).mp hdeg x
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hsurj hg
  exact ⟨a, ha⟩

private theorem Gauss.inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S)
    (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have hinv : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  exact hinv ▸ SetLike.coe_mem _

private theorem Gauss.coe_unit_inv {S : ValuationSubring F} (u : Sˣ) :
    (((u⁻¹ : Sˣ) : S) : F) = ((u : S) : F)⁻¹ := by
  have h1 : ((u : S) : F) * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (inv_eq_of_mul_eq_one_right h1).symm

private theorem Gauss.exists_coeffMap_subtype_eq {L : Type*} [Field L] (A : ValuationSubring L)
    (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq]
    rw [← ZeroMemClass.coe_eq_zero]
  · ext n
    rfl

private theorem Gauss.coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

private theorem Gauss.coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

private theorem Gauss.smul_divisor_eq_of_forall_mem_support {g : SemilinearAut K F} {E : Divisor K F}
    (h : ∀ W ∈ E.support, g • W = W) : g • E = E :=
  calc g • E = Finsupp.mapDomain (g • ·) E := SemilinearAut.divisor_smul_def g E
    _ = Finsupp.mapDomain id E := Finsupp.mapDomain_congr fun W hW => h W hW
    _ = E := Finsupp.mapDomain_id

private theorem Gauss.smul_inv_eq_of_smul_eq {g : SemilinearAut K F} {U : F} (hU : g • U = U) : g • U⁻¹ = U⁻¹ := by
  rw [SemilinearAut.smul_def, map_inv₀, ← SemilinearAut.smul_def, hU]

end Generic

section Level

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]

local notation "F" => modularFunctionFieldBar (N * q)
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "w" => ProlongationTuple.atkinLehnerBar N q
local notation "J" => ProlongationTuple.jFun N q
local notation "JQ" => ProlongationTuple.jQFun N q

private theorem Gauss.neZero : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩

private theorem Gauss.w_jFun_and_w_jQFun (hqN : ¬ q ∣ N) : w J = JQ ∧ w JQ = J := by
  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨hleg1, hleg2⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hAL
  let jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q jN = J :=
    Subtype.ext (coe_heckeAlphaBar N q jN)
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q jN = JQ :=
    Subtype.ext (coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm
  refine ⟨?_, ?_⟩
  · rw [← hαj, ← hβj]; exact DFunLike.congr_fun hleg1 jN
  · rw [← hαj, ← hβj]; exact DFunLike.congr_fun hleg2 jN

private theorem Gauss.w_jFun (hqN : ¬ q ∣ N) : w J = JQ := (Gauss.w_jFun_and_w_jQFun hqN).1
private theorem Gauss.w_jQFun (hqN : ¬ q ∣ N) : w JQ = J := (Gauss.w_jFun_and_w_jQFun hqN).2
private theorem Gauss.winv_jFun (hqN : ¬ q ∣ N) : w⁻¹ J = JQ := by
  have h := Gauss.w_jQFun (N := N) hqN
  conv_lhs => rw [← h]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem Gauss.winv_jQFun (hqN : ¬ q ∣ N) : w⁻¹ JQ = J := by
  have h := Gauss.w_jFun (N := N) hqN
  conv_lhs => rw [← h]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem Gauss.ord_w (W : Place ℚ̄ F) (g : F) : W.ord (w g) = (w⁻¹ • W).ord g := by
  conv_lhs => rw [← smul_inv_smul w W]
  rw [Place.ord_smul]

private theorem Gauss.ord_winv (W : Place ℚ̄ F) (g : F) : W.ord (w⁻¹ g) = (w • W).ord g := by
  conv_lhs => rw [← inv_smul_smul w W]
  rw [Place.ord_smul]

private theorem Gauss.coe_jFun : ((J : F) : LaurentSeries ℚ̄) = jqModC ℚ̄ := by
  show coeffMap (algebraMap ℚ ℚ̄) jq = _
  rw [← jqModC_rat]
  exact Gauss.coeffMap_jqModC _

private theorem Gauss.coe_jQFun : ((JQ : F) : LaurentSeries ℚ̄) = qExpand ℚ̄ q (jqModC ℚ̄) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show coeffMap (algebraMap ℚ ℚ̄) (qExpand ℚ q jq) = _
  rw [coeffMap_qExpand, ← jqModC_rat, Gauss.coeffMap_jqModC]

private theorem Gauss.coe_algebraMap (c : ℚ̄) :
    ((algebraMap ℚ̄ F c : F) : LaurentSeries ℚ̄) = HahnSeries.single 0 c := by
  rw [show ((algebraMap ℚ̄ F c : F) : LaurentSeries ℚ̄) = algebraMap ℚ̄ (LaurentSeries ℚ̄) c from rfl,
    algebraMap_laurentSeries_eq_single]

private theorem Gauss.jFun_ne_algebraMap (c : ℚ̄) : (J : F) ≠ algebraMap ℚ̄ F c := by
  intro h
  have h1 := congrArg (fun x : F => (x : LaurentSeries ℚ̄).coeff (-1)) h
  simp only [Gauss.coe_jFun, Gauss.coe_algebraMap] at h1
  rw [HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide), coeff_jqModC_neg_one] at h1
  exact one_ne_zero h1

private theorem Gauss.jQFun_ne_algebraMap (c : ℚ̄) : (JQ : F) ≠ algebraMap ℚ̄ F c := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro h
  have h1 := congrArg (fun x : F => (x : LaurentSeries ℚ̄).coeff ((q : ℤ) * (-1))) h
  simp only [Gauss.coe_jQFun, Gauss.coe_algebraMap] at h1
  rw [qExpand_coeff_mul, HahnSeries.coeff_single_of_ne, coeff_jqModC_neg_one] at h1
  · exact one_ne_zero h1
  · have : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    omega

private theorem Gauss.jFun_ne_zero : (J : F) ≠ 0 := by simpa using Gauss.jFun_ne_algebraMap (N := N) (q := q) 0
private theorem Gauss.jQFun_ne_zero : (JQ : F) ≠ 0 := by simpa using Gauss.jQFun_ne_algebraMap (N := N) (q := q) 0

private theorem Gauss.galois_smul_algebraMap (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (c : ℚ̄) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • algebraMap ℚ̄ F c = algebraMap ℚ̄ F (σ c) :=
  (SemilinearAut.smul_algebraMap _ c).trans rfl

private theorem Gauss.galois_smul_jFun (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (J : F) = J := by
  apply Subtype.ext
  show coeffMap (σ : ℚ̄ →+* ℚ̄) ((J : F) : LaurentSeries ℚ̄) = ((J : F) : LaurentSeries ℚ̄)
  rw [Gauss.coe_jFun, Gauss.coeffMap_jqModC]

private theorem Gauss.galois_smul_jQFun (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (JQ : F) = JQ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  apply Subtype.ext
  show coeffMap (σ : ℚ̄ →+* ℚ̄) ((JQ : F) : LaurentSeries ℚ̄) = ((JQ : F) : LaurentSeries ℚ̄)
  rw [Gauss.coe_jQFun, coeffMap_qExpand, Gauss.coeffMap_jqModC]

private theorem Gauss.eq_of_ord_sub_one_pos (W : Place ℚ̄ F) (g : F) {c c' : ℚ̄}
    (hc : 0 < W.ord (algebraMap ℚ̄ F c * g - 1)) (hc' : 0 < W.ord (algebraMap ℚ̄ F c' * g - 1)) : c = c' := by
  have hval : ∀ a : ℚ̄, 0 < W.ord (algebraMap ℚ̄ F a * g - 1) → W.HasValue g a⁻¹ := by
    intro a ha
    have h0 : W.HasValue (algebraMap ℚ̄ F a * g - 1) 0 := Eval.hasValue_zero_of_ord_pos W (Or.inr ha)
    have h1 : W.HasValue (algebraMap ℚ̄ F a * g - 1 + 1) (0 + 1) := Eval.hvAdd h0 (Place.hasValue_one W)
    rw [sub_add_cancel, zero_add] at h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at h1
      exact zero_ne_one ((Eval.hasValue_zero W).unique h1)
    have h2 : W.HasValue (algebraMap ℚ̄ F a⁻¹ * (algebraMap ℚ̄ F a * g)) (a⁻¹ * 1) :=
      (Place.hasValue_algebraMap W a⁻¹).mul h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul, mul_one] at h2
  exact inv_injective ((hval c hc).unique (hval c' hc'))

private theorem Gauss.eval₂_modularPolynomial (data : ModularPolynomialData q) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) J)).eval JQ = 0 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have key := eval_int_eq_zero_geom ℚ̄ (N := q) data
  set θ : F →+* LaurentSeries ℚ̄ := (modularFunctionFieldBar (N * q)).toSubalgebra.val.toRingHom with hθ
  have hθ' : ∀ x : F, θ x = (x : LaurentSeries ℚ̄) := fun x => rfl
  have hcomp : θ.comp (Polynomial.eval₂RingHom (Int.castRingHom F) J) = evalAtJGeom ℚ̄ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [evalAtJGeom]
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJGeom_X, hθ',
        Gauss.coe_jFun]
  have hJQ : θ JQ = jqNModC (AlgebraicClosure ℚ) q := by
    rw [hθ']
    exact Gauss.coe_jQFun (N := N) (q := q)
  apply Subtype.val_injective
  rw [ZeroMemClass.coe_zero, ← hθ', Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, hJQ]
  exact key

private theorem Gauss.mem_of_eval₂_modularPolynomial (data : ModularPolynomialData q) (W : Place ℚ̄ F) {x y : F}
    (hx : x ∈ W.toValuationSubring)
    (hxy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)).eval y = 0) :
    y ∈ W.toValuationSubring := by
  set p : Polynomial W.toValuationSubring :=
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom W.toValuationSubring) ⟨x, hx⟩) with hp
  have hmonic : p.Monic := data.monic.map _
  have hmap : p.map (algebraMap W.toValuationSubring F) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x) := by
    rw [hp, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hint : IsIntegral W.toValuationSubring y := by
    refine ⟨p, hmonic, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hmap]
    exact hxy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hz ▸ z.2

private def Gauss.IsCusp (W : Place ℚ̄ F) : Prop := W.ord (J : F) < 0

private theorem Gauss.jQFun_mem_of_jFun_mem (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (h : (J : F) ∈ W.toValuationSubring) : (JQ : F) ∈ W.toValuationSubring :=
  Gauss.mem_of_eval₂_modularPolynomial data W h (Gauss.eval₂_modularPolynomial data)

private theorem Gauss.eval₂_modularPolynomial' (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) JQ)).eval J = 0 := by
  have h := congrArg (w : F → F) (Gauss.eval₂_modularPolynomial (N := N) data)
  simp only [map_zero] at h
  rw [Polynomial.eval_map, ← AlgEquiv.coe_ringEquiv, ← RingEquiv.coe_toRingHom, Polynomial.hom_eval₂] at h
  rw [Polynomial.eval_map]
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | rfl | (refine Polynomial.ringHom_ext (fun a => by simp) ?_; first | simp [Gauss.w_jFun hqN] | simp [Gauss.w_jQFun hqN]) | simp [Gauss.w_jQFun hqN] | simp [Gauss.w_jFun hqN] | (symm; simp [Gauss.w_jQFun hqN]) | (symm; simp [Gauss.w_jFun hqN]) | skip

private theorem Gauss.jFun_mem_of_jQFun_mem (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (h : (JQ : F) ∈ W.toValuationSubring) : (J : F) ∈ W.toValuationSubring :=
  Gauss.mem_of_eval₂_modularPolynomial data W h (Gauss.eval₂_modularPolynomial' hqN data)

private theorem Gauss.ord_jQFun_neg_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    W.ord (JQ : F) < 0 ↔ Gauss.IsCusp W := by
  unfold Gauss.IsCusp
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have hm := Gauss.jQFun_mem_of_jFun_mem data W (Gauss.mem_of_ord_nonneg W Gauss.jFun_ne_zero h')
    exact absurd (Gauss.ord_nonneg_of_mem W Gauss.jQFun_ne_zero hm) (not_le.mpr h)
  · intro h
    by_contra h'
    push Not at h'
    have hm := Gauss.jFun_mem_of_jQFun_mem hqN data W (Gauss.mem_of_ord_nonneg W Gauss.jQFun_ne_zero h')
    exact absurd (Gauss.ord_nonneg_of_mem W Gauss.jFun_ne_zero hm) (not_le.mpr h)

private theorem Gauss.isCusp_smul_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    Gauss.IsCusp (w • W) ↔ Gauss.IsCusp W := by
  show (w • W).ord J < 0 ↔ _
  rw [← Gauss.ord_winv, Gauss.winv_jFun hqN]
  exact Gauss.ord_jQFun_neg_iff hqN data W

private theorem Gauss.isCusp_winv_smul_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    Gauss.IsCusp (w⁻¹ • W) ↔ Gauss.IsCusp W := by
  show (w⁻¹ • W).ord J < 0 ↔ _
  rw [← Gauss.ord_w, Gauss.w_jFun hqN]
  exact Gauss.ord_jQFun_neg_iff hqN data W

private noncomputable def Gauss.uJ (b : A) : F :=
  algebraMap ℚ̄ F (b : ℚ̄) * J - 1

private noncomputable def Gauss.uJq (b : A) : F :=
  algebraMap ℚ̄ F (b : ℚ̄) * JQ - 1

private theorem Gauss.w_uJ (hqN : ¬ q ∣ N) (b : A) : w (Gauss.uJ (N := N) (q := q) b) = Gauss.uJq b := by
  unfold Gauss.uJ Gauss.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Gauss.w_jFun hqN]

private theorem Gauss.w_uJq (hqN : ¬ q ∣ N) (b : A) : w (Gauss.uJq (N := N) (q := q) b) = Gauss.uJ b := by
  unfold Gauss.uJ Gauss.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Gauss.w_jQFun hqN]

private theorem Gauss.galois_smul_uJ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (b : A) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gauss.uJ (N := N) (q := q) b
      = algebraMap ℚ̄ F (σ (b : ℚ̄)) * J - 1 := by
  unfold Gauss.uJ
  rw [smul_sub, smul_mul', smul_one, Gauss.galois_smul_algebraMap, Gauss.galois_smul_jFun]

private theorem Gauss.galois_smul_uJq (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (b : A) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gauss.uJq (N := N) (q := q) b
      = algebraMap ℚ̄ F (σ (b : ℚ̄)) * JQ - 1 := by
  unfold Gauss.uJq
  rw [smul_sub, smul_mul', smul_one, Gauss.galois_smul_algebraMap, Gauss.galois_smul_jQFun]

private theorem Gauss.coe_uJ (b : A) :
    ((Gauss.uJ (N := N) (q := q) b : F) : LaurentSeries ℚ̄) = coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) := by
  rw [map_sub, map_mul, map_one, Gauss.coeffMap_C, Gauss.coeffMap_jqModC]
  unfold Gauss.uJ
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Gauss.coe_jFun, Gauss.coe_algebraMap,
    HahnSeries.C_apply]
  rfl

private theorem Gauss.coe_uJq (b : A) :
    ((Gauss.uJq (N := N) (q := q) b : F) : LaurentSeries ℚ̄) =
      coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [map_sub, map_mul, map_one, Gauss.coeffMap_C, coeffMap_qExpand, Gauss.coeffMap_jqModC]
  unfold Gauss.uJq
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Gauss.coe_jQFun, Gauss.coe_algebraMap,
    HahnSeries.C_apply]
  rfl

private theorem Gauss.coeffMap_residue_yJ (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * jqModC A - 1) = -1 := by
  rw [map_sub, map_mul, map_one, Gauss.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

private theorem Gauss.coeffMap_residue_yJq (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * qExpand A q (jqModC A) - 1) = -1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [map_sub, map_mul, map_one, Gauss.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

private theorem Gauss.isCusp_of_ord_uJ_neg (b : A) (W : Place ℚ̄ F) (h : W.ord (Gauss.uJ (N := N) (q := q) b) < 0) :
    Gauss.IsCusp W := by
  have h1 : W.ord (algebraMap ℚ̄ F (b : ℚ̄) * J) < 0 := Gauss.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : ℚ̄) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Gauss.jFun_ne_zero, Gauss.ord_algebraMap, zero_add] at h1
  exact h1

private theorem Gauss.isCusp_of_ord_uJq_neg (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (b : A) (W : Place ℚ̄ F)
    (h : W.ord (Gauss.uJq (N := N) (q := q) b) < 0) : Gauss.IsCusp W := by
  have h1 : W.ord (algebraMap ℚ̄ F (b : ℚ̄) * JQ) < 0 := Gauss.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : ℚ̄) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Gauss.jQFun_ne_zero, Gauss.ord_algebraMap, zero_add] at h1
  exact (Gauss.ord_jQFun_neg_iff hqN data W).mp h1

private theorem Gauss.uJ_ne_zero (b : A) : Gauss.uJ (N := N) (q := q) b ≠ 0 := by
  intro h
  have h' : algebraMap ℚ̄ F (b : ℚ̄) * J = 1 := sub_eq_zero.mp h
  rcases eq_or_ne (b : ℚ̄) 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · apply Gauss.jFun_ne_algebraMap (N := N) (q := q) ((b : ℚ̄)⁻¹)
    rw [← mul_right_inj' ((map_ne_zero (algebraMap ℚ̄ F)).mpr hb), h', ← map_mul, mul_inv_cancel₀ hb, map_one]

private theorem Gauss.uJq_ne_zero (b : A) : Gauss.uJq (N := N) (q := q) b ≠ 0 := by
  intro h
  have h' : algebraMap ℚ̄ F (b : ℚ̄) * JQ = 1 := sub_eq_zero.mp h
  rcases eq_or_ne (b : ℚ̄) 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · apply Gauss.jQFun_ne_algebraMap (N := N) (q := q) ((b : ℚ̄)⁻¹)
    rw [← mul_right_inj' ((map_ne_zero (algebraMap ℚ̄ F)).mpr hb), h', ← map_mul, mul_inv_cancel₀ hb, map_one]

private theorem Gauss.uJ_mem_place (b : A) {W : Place ℚ̄ F} (hW : ¬ Gauss.IsCusp W) :
    Gauss.uJ (N := N) (q := q) b ∈ W.toValuationSubring :=
  Gauss.mem_of_ord_nonneg W (Gauss.uJ_ne_zero b) (not_lt.mp fun h => hW (Gauss.isCusp_of_ord_uJ_neg b W h))

private theorem Gauss.uJq_mem_place (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (b : A) {W : Place ℚ̄ F}
    (hW : ¬ Gauss.IsCusp W) : Gauss.uJq (N := N) (q := q) b ∈ W.toValuationSubring :=
  Gauss.mem_of_ord_nonneg W (Gauss.uJq_ne_zero b)
    (not_lt.mp fun h => hW (Gauss.isCusp_of_ord_uJq_neg hqN data b W h))

private theorem Gauss.exists_uJ_of_tate (W : Place ℚ̄ F) (hW : ¬ Gauss.IsCusp W)
    (hcusp : ∀ a : A, W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Gauss.uJ (N := N) (q := q) b) := by
  haveI : NeZero (N * q) := Gauss.neZero
  have hj0 : 0 ≤ W.ord (J : F) := not_lt.mp hW
  have hmem : (J : F) ∈ W.toValuationSubring := Gauss.mem_of_ord_nonneg W Gauss.jFun_ne_zero hj0
  obtain ⟨c, hc⟩ := Gauss.exists_hasValue_of_deg_eq_one W (deg_eq_one_modularFunctionFieldBar (N * q) W) hmem
  have hpos : 0 < W.ord ((J : F) - algebraMap _ _ c) :=
    Gauss.ord_sub_pos_of_hasValue W hc (Gauss.jFun_ne_algebraMap c)
  have hcA : c ∉ A := fun hcA => absurd (hcusp ⟨c, hcA⟩) (not_le.mpr hpos)
  have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
  have hbA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  refine ⟨⟨c⁻¹, hbA⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hcA
    have h2 := Gauss.inv_mem_of_isUnit hbA hu
    rwa [inv_inv] at h2
  · have e : Gauss.uJ (N := N) (q := q) ⟨c⁻¹, hbA⟩ = algebraMap _ _ (c⁻¹ : ℚ̄) * ((J : F) - algebraMap _ _ c) := by
      unfold Gauss.uJ
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [e, W.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hc0)) (sub_ne_zero.mpr (Gauss.jFun_ne_algebraMap c)),
      Gauss.ord_algebraMap, zero_add]
    exact hpos

private theorem Gauss.exists_uJq_of_tate (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (hW : ¬ Gauss.IsCusp W)
    (hcusp : ∀ a : A, W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Gauss.uJq (N := N) (q := q) b) := by

  have h' : ∀ a : A, (w⁻¹ • W).ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0 := by
    intro a
    have e : w ((J : F) - algebraMap _ _ (a : ℚ̄)) = (JQ : F) - algebraMap _ _ (a : ℚ̄) := by
      rw [map_sub, Gauss.w_jFun hqN, AlgEquiv.commutes]
    rw [← Gauss.ord_w, e]
    exact hcusp a
  have hW' : ¬ Gauss.IsCusp (w⁻¹ • W) := by rwa [Gauss.isCusp_winv_smul_iff hqN data]
  obtain ⟨b, hb, hpos⟩ := Gauss.exists_uJ_of_tate (N := N) (q := q) _ hW' h'
  refine ⟨b, hb, ?_⟩
  rw [← Gauss.w_uJ hqN, Gauss.ord_w]
  exact hpos

private theorem Gauss.exists_coeffMap_eq_smul_of_poles (f : F) (hf : f ≠ 0)
    (hpole : ∀ W : Place ℚ̄ F, W.ord f < 0 →
      (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Gauss.IsCusp W) :
    ∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧ coeffMap A.subtype y = c • (f : LaurentSeries ℚ̄) := by
  classical
  haveI : NeZero (N * q) := Gauss.neZero
  have hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) f hf
  set M : ℕ := ∑ W ∈ D.support, (-(D W)).toNat with hM
  have hMb : ∀ W : Place ℚ̄ F, -(W.ord f) ≤ M := by
    intro W
    by_cases hW : W ∈ D.support
    · have h1 : (-(D W)).toNat ≤ M :=
        Finset.single_le_sum (f := fun W' => (-(D W')).toNat) (fun _ _ => Nat.zero_le _) hW
      have h2 : -(D W) ≤ ((-(D W)).toNat : ℤ) := Int.self_le_toNat _
      rw [← hD]; omega
    · have : D W = 0 := Finsupp.notMem_support_iff.mp hW
      rw [← hD, this]; omega
  have hJ0 : (J : F)⁻¹ ^ M ≠ 0 := pow_ne_zero _ (inv_ne_zero Gauss.jFun_ne_zero)
  have hg0 : f * (J : F)⁻¹ ^ M ≠ 0 := mul_ne_zero hf hJ0
  have hordg : ∀ W : Place ℚ̄ F, W.ord (f * (J : F)⁻¹ ^ M) = W.ord f - M * W.ord (J : F) := fun W => by
    rw [W.ord_mul hf hJ0, Gauss.ord_pow, W.ord_inv]; ring
  obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (N * q) _ hg0 (by
    intro W hW
    rw [hordg] at hW
    rcases lt_trichotomy (W.ord (J : F)) 0 with hj | hj | hj
    · exfalso
      have h1 := hMb W
      have h2 : (M : ℤ) * W.ord (J : F) ≤ (M : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg M)
      omega
    · rw [hj, mul_zero, sub_zero] at hW
      rcases hpole W hW with h | h
      · exact h
      · exact absurd h (by unfold Gauss.IsCusp; omega)
    · refine ⟨0, ?_⟩
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
      exact hj)
  obtain ⟨yg, hyg⟩ := Gauss.exists_coeffMap_subtype_eq A _ hc
  have hJne : jqModC ℚ̄ ≠ 0 := by
    rw [← Gauss.coe_jFun (N := N) (q := q)]
    exact fun h => Gauss.jFun_ne_zero (N := N) (q := q) ((ZeroMemClass.coe_eq_zero).mp h)
  have hJJ : ((jqModC ℚ̄)⁻¹) ^ M * (jqModC ℚ̄) ^ M = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hJne, one_pow]
  refine ⟨c, yg * (jqModC A) ^ M, hc0, ?_⟩
  rw [map_mul, map_pow, hyg, Gauss.coeffMap_jqModC, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
    IntermediateField.coe_inv, Gauss.coe_jFun, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    mul_assoc, mul_assoc, hJJ, mul_one]

private theorem Gauss.poles_mul (E : Divisor ℚ̄ F) (U : F) (hU0 : U ≠ 0)
    (hUint : ∀ W : Place ℚ̄ F, ¬ Gauss.IsCusp W → U ∈ W.toValuationSubring)
    (T : Place ℚ̄ F → Prop)
    (hUT : ∀ W : Place ℚ̄ F, ¬ Gauss.IsCusp W → 0 < E W → T W → E W ≤ W.ord U)
    (f : F) (hf : f ∈ riemannRochSpace E) (hf0 : f ≠ 0)
    (W : Place ℚ̄ F) (hW : W.ord (U * f) < 0) :
    ¬ T W ∨ Gauss.IsCusp W := by
  by_cases hc : Gauss.IsCusp W
  · exact Or.inr hc
  left
  intro hT
  have hU : 0 ≤ W.ord U := Gauss.ord_nonneg_of_mem W hU0 (hUint W hc)
  rw [W.ord_mul hU0 hf0] at hW
  rcases (mem_riemannRochSpace_iff.mp hf) W with h | h
  · exact hf0 h
  · have hEW : 0 < E W := by omega
    have h2 := hUT W hc hEW hT
    omega

end Level

section Pair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

local notation "F" => modularFunctionFieldBar (N * q)
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "w" => ProlongationTuple.atkinLehnerBar N q
local notation "J" => ProlongationTuple.jFun N q
local notation "JQ" => ProlongationTuple.jQFun N q

private theorem Gauss.uJ_mem₁ (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Gauss.uJ (N := N) (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Gauss.uJ b, h⟩ = -1 := by
  have hy : coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) ∈ F := by
    rw [← Gauss.coe_uJ (N := N) (q := q)]; exact (Gauss.uJ (N := N) (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * jqModC A - 1), hy⟩ : F) = Gauss.uJ b :=
    Subtype.ext (Gauss.coe_uJ b).symm
  have h' : Gauss.uJ (N := N) (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Gauss.uJ b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Gauss.coeffMap_residue_yJ b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

private theorem Gauss.uJq_mem₁ (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Gauss.uJq (N := N) (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Gauss.uJq b, h⟩ = -1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hy : coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1) ∈ F := by
    rw [← Gauss.coe_uJq (N := N) (q := q)]; exact (Gauss.uJq (N := N) (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1), hy⟩ : F) = Gauss.uJq b :=
    Subtype.ext (Gauss.coe_uJq b).symm
  have h' : Gauss.uJq (N := N) (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Gauss.uJq b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Gauss.coeffMap_residue_yJq b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

private theorem Gauss.uJ_mem₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Gauss.uJ (N := N) (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Gauss.uJ b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Gauss.uJq_mem₁ R b hb
  have h1' : w (Gauss.uJ (N := N) (q := q) b) ∈ R.R₁.integers := by
    rw [Gauss.w_uJ hqN]; exact h1
  have h2 : Gauss.uJ (N := N) (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨w (Gauss.uJ b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers) = ⟨Gauss.uJq b, h1⟩ :=
    Subtype.ext (Gauss.w_uJ hqN b)
  rw [e, hres]

private theorem Gauss.uJq_mem₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Gauss.uJq (N := N) (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Gauss.uJq b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Gauss.uJ_mem₁ R b hb
  have h1' : w (Gauss.uJq (N := N) (q := q) b) ∈ R.R₁.integers := by
    rw [Gauss.w_uJq hqN]; exact h1
  have h2 : Gauss.uJq (N := N) (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨w (Gauss.uJq b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers) = ⟨Gauss.uJ b, h1⟩ :=
    Subtype.ext (Gauss.w_uJq hqN b)
  rw [e, hres]

private noncomputable def Gauss.bigU (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A) :
    F :=
  (∏ W ∈ E.support, Gauss.uJ (N := N) (q := q) (bJ W) ^ (E W).toNat) *
    ∏ W ∈ E.support, Gauss.uJq (N := N) (q := q) (bJq W) ^ (E W).toNat

private theorem Gauss.bigU_ne_zero (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A) :
    Gauss.bigU (N := N) (q := q) E bJ bJq ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Gauss.uJ_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Gauss.uJq_ne_zero _))

private theorem Gauss.bigU_mem_place (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Gauss.IsCusp W) :
    Gauss.bigU (N := N) (q := q) E bJ bJq ∈ W.toValuationSubring :=
  mul_mem (prod_mem fun W' _ => pow_mem (Gauss.uJ_mem_place _ hWc) _)
    (prod_mem fun W' _ => pow_mem (Gauss.uJq_mem_place hqN data _ hWc) _)

private theorem Gauss.galois_smul_bigU (E : Divisor ℚ̄ F) (bJ bJq : Place ℚ̄ F → A) (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    (hbJ : ∀ W ∈ E.support, σ (bJ W : ℚ̄) = bJ W) (hbJq : ∀ W ∈ E.support, σ (bJq W : ℚ̄) = bJq W) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gauss.bigU (N := N) (q := q) E bJ bJq
      = Gauss.bigU E bJ bJq := by
  unfold Gauss.bigU
  rw [smul_mul', Finset.smul_prod', Finset.smul_prod']
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun W hW => ?_) (Finset.prod_congr rfl fun W hW => ?_)
  · rw [smul_pow', Gauss.galois_smul_uJ, hbJ W hW]
    rfl
  · rw [smul_pow', Gauss.galois_smul_uJq, hbJq W hW]
    rfl

private theorem Gauss.le_ord_bigU_of_pos (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Gauss.IsCusp W) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Gauss.uJ (N := N) (q := q) (bJ W))) :
    E W ≤ W.ord (Gauss.bigU (N := N) (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Gauss.uJ (N := N) (q := q) (bJ W') ^ (E W').toNat) hWS
  unfold Gauss.bigU
  rw [← hsplit]
  have hne1 : Gauss.uJ (N := N) (q := q) (bJ W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Gauss.uJ_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Gauss.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Gauss.uJ_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Gauss.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Gauss.uJq_ne_zero _)
  rw [W.ord_mul (mul_ne_zero hne1 hne2) hne3, W.ord_mul hne1 hne2, Gauss.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Gauss.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat) :=
    Gauss.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Gauss.uJ_mem_place _ hWc) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Gauss.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat) :=
    Gauss.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Gauss.uJq_mem_place hqN data _ hWc) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Gauss.uJ (N := N) (q := q) (bJ W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

private theorem Gauss.le_ord_bigU_of_pos' (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Gauss.IsCusp W) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Gauss.uJq (N := N) (q := q) (bJq W))) :
    E W ≤ W.ord (Gauss.bigU (N := N) (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Gauss.uJq (N := N) (q := q) (bJq W') ^ (E W').toNat) hWS
  unfold Gauss.bigU
  rw [← hsplit]
  have hne1 : Gauss.uJq (N := N) (q := q) (bJq W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Gauss.uJq_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Gauss.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Gauss.uJq_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Gauss.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Gauss.uJ_ne_zero _)
  rw [W.ord_mul hne3 (mul_ne_zero hne1 hne2), W.ord_mul hne1 hne2, Gauss.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Gauss.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat) :=
    Gauss.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Gauss.uJq_mem_place hqN data _ hWc) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Gauss.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat) :=
    Gauss.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Gauss.uJ_mem_place _ hWc) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Gauss.uJq (N := N) (q := q) (bJq W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

private theorem Gauss.bigU_isUnit₁ (R : ProlongationTuple P)
    (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Gauss.bigU (N := N) (q := q) E bJ bJq ∈ R.R₁.integers, IsUnit (⟨Gauss.bigU E bJ bJq, h⟩ : R.R₁.integers) := by
  classical
  have m1 : ∀ W, Gauss.uJ (N := N) (q := q) (bJ W) ∈ R.R₁.integers := fun W => (Gauss.uJ_mem₁ R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Gauss.uJq (N := N) (q := q) (bJq W) ∈ R.R₁.integers := fun W => (Gauss.uJq_mem₁ R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₁.residue ⟨Gauss.uJ (N := N) (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Gauss.uJ_mem₁ R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₁.residue ⟨Gauss.uJq (N := N) (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Gauss.uJq_mem₁ R (bJq W) (hbJq W)).2
  set y1 : Place ℚ̄ F → R.R₁.integers :=
    fun W => ⟨Gauss.uJ (N := N) (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place ℚ̄ F → R.R₁.integers :=
    fun W => ⟨Gauss.uJq (N := N) (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₁.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₁.integers) : F)
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₁.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₁.integers) : F)
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₁.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : F) = Gauss.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Gauss.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Gauss.bigU (N := N) (q := q) E bJ bJq ∈ R.R₁.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Gauss.bigU E bJ bJq, hmem⟩ : R.R₁.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₁.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

private theorem Gauss.bigU_isUnit₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Gauss.bigU (N := N) (q := q) E bJ bJq ∈ R.R₂.integers, IsUnit (⟨Gauss.bigU E bJ bJq, h⟩ : R.R₂.integers) := by
  classical
  have m1 : ∀ W, Gauss.uJ (N := N) (q := q) (bJ W) ∈ R.R₂.integers := fun W => (Gauss.uJ_mem₂ hqN R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Gauss.uJq (N := N) (q := q) (bJq W) ∈ R.R₂.integers := fun W => (Gauss.uJq_mem₂ hqN R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₂.residue ⟨Gauss.uJ (N := N) (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Gauss.uJ_mem₂ hqN R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₂.residue ⟨Gauss.uJq (N := N) (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Gauss.uJq_mem₂ hqN R (bJq W) (hbJq W)).2
  set y1 : Place ℚ̄ F → R.R₂.integers :=
    fun W => ⟨Gauss.uJ (N := N) (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place ℚ̄ F → R.R₂.integers :=
    fun W => ⟨Gauss.uJq (N := N) (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₂.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₂.integers) : F)
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₂.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₂.integers) : F)
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₂.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : F) = Gauss.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Gauss.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Gauss.bigU (N := N) (q := q) E bJ bJq ∈ R.R₂.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Gauss.bigU E bJ bJq, hmem⟩ : R.R₂.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₂.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

private theorem Gauss.exists_bigU (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (S : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (E : Divisor ℚ̄ F)
    (hEfix : ∀ W ∈ E.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W = W) :
    ∃ U : F,
      (∃ h₁ : U ∈ R.R₁.integers, IsUnit (⟨U, h₁⟩ : R.R₁.integers)) ∧
      (∃ h₂ : U ∈ R.R₂.integers, IsUnit (⟨U, h₂⟩ : R.R₂.integers)) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord ((J : F)
            - algebraMap (AlgebraicClosure ℚ) (F) (a : AlgebraicClosure ℚ)))
          ∨ Gauss.IsCusp W) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord ((JQ : F)
            - algebraMap (AlgebraicClosure ℚ) (F) (a : AlgebraicClosure ℚ)))
          ∨ Gauss.IsCusp W) ∧
      (∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U) := by
  classical

  have hJ : ∀ W : Place ℚ̄ F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ Gauss.IsCusp W →
        (∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Gauss.uJ (N := N) (q := q) b)) ∧
      (b = 0 ∨ 0 < W.ord (Gauss.uJ (N := N) (q := q) b)) := by
    intro W
    by_cases h : ¬ Gauss.IsCusp W ∧
        ∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Gauss.exists_uJ_of_tate W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos, Or.inr hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h, Or.inl rfl⟩
  have hJq : ∀ W : Place ℚ̄ F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ Gauss.IsCusp W →
        (∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Gauss.uJq (N := N) (q := q) b)) ∧
      (b = 0 ∨ 0 < W.ord (Gauss.uJq (N := N) (q := q) b)) := by
    intro W
    by_cases h : ¬ Gauss.IsCusp W ∧
        ∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Gauss.exists_uJq_of_tate hqN data W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos, Or.inr hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h, Or.inl rfl⟩
  choose bJ hbJm hbJpos hbJfix using hJ
  choose bJq hbJqm hbJqpos hbJqfix using hJq
  refine ⟨Gauss.bigU E bJ bJq, Gauss.bigU_isUnit₁ R E bJ bJq hbJm hbJqm,
    Gauss.bigU_isUnit₂ hqN R E bJ bJq hbJm hbJqm, ?_, ?_, ?_⟩
  · intro f hf hf0 W hW
    rcases Gauss.poles_mul E _ (Gauss.bigU_ne_zero E bJ bJq) (Gauss.bigU_mem_place hqN data E bJ bJq)
      (fun W => ∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hWc hEW hT => Gauss.le_ord_bigU_of_pos hqN data E bJ bJq W hWc hEW (hbJpos W hWc hT))
      f hf hf0 W hW with h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr h
  · intro f hf hf0 W hW
    rcases Gauss.poles_mul E _ (Gauss.bigU_ne_zero E bJ bJq) (Gauss.bigU_mem_place hqN data E bJ bJq)
      (fun W => ∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hWc hEW hT => Gauss.le_ord_bigU_of_pos' hqN data E bJ bJq W hWc hEW (hbJqpos W hWc hT))
      f hf hf0 W hW with h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr h
  ·
    intro σ hσ
    refine Gauss.galois_smul_bigU E bJ bJq σ (fun W hW => ?_) (fun W hW => ?_)
    · rcases hbJfix W with h | h
      · rw [h, ZeroMemClass.coe_zero, map_zero]
      · have ht := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) W
          (Gauss.uJ (N := N) (q := q) (bJ W))
        rw [hEfix W hW σ hσ, Gauss.galois_smul_uJ] at ht
        exact Gauss.eq_of_ord_sub_one_pos W (J : F) (by rw [ht]; exact h) h
    · rcases hbJqfix W with h | h
      · rw [h, ZeroMemClass.coe_zero, map_zero]
      · have ht := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) W
          (Gauss.uJq (N := N) (q := q) (bJq W))
        rw [hEfix W hW σ hσ, Gauss.galois_smul_uJq] at ht
        exact Gauss.eq_of_ord_sub_one_pos W (JQ : F) (by rw [ht]; exact h) h

private theorem Gauss.linearIndependent_mul_units {k₀ L : Type*} [Field k₀] [Field L] [Algebra k₀ L]
    {ι : Type*} {r : ι → L × L} (hr : LinearIndependent k₀ r) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent k₀ (fun i => (a * (r i).1, b * (r i).2)) := by
  let φ : L × L →ₗ[k₀] L × L := (LinearMap.mulLeft k₀ a).prodMap (LinearMap.mulLeft k₀ b)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    simp only [φ, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ ha h.1) (mul_left_cancel₀ hb h.2)
  have h := hr.map' φ hφ
  exact h

private theorem Gauss.hint (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (S : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (E : Divisor ℚ̄ F) [FiniteDimensional ℚ̄ ↥(riemannRochSpace E)]
    (hE : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E)
    (U : F) (hU0 : U ≠ 0)
    (hUfix : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U)
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Gauss.IsCusp W)
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Gauss.IsCusp W)
    (V : Submodule ℚ̄ F) (hV : V = (riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))
    [FiniteDimensional ℚ̄ V] :
    ∃ b : Fin (Module.finrank ℚ̄ V) → F,
      (∀ i, b i ∈ V) ∧ LinearIndependent ℚ̄ b ∧
      (∀ i, (∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : F) : LaurentSeries ℚ̄)) ∧
           (∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((w (b i) : F) : LaurentSeries ℚ̄))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • b i = b i := by
  classical
  haveI : NeZero (N * q) := Gauss.neZero
  have hinj : Function.Injective (LinearMap.mulLeft ℚ̄ U) := by
    intro x y h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hU0 h
  have hn : Module.finrank ℚ̄ V = Module.finrank ℚ̄ ↥(riemannRochSpace E) := by
    rw [hV]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (riemannRochSpace E))).symm
  obtain ⟨b₀, hb₀V, hb₀li, hb₀fix⟩ :=
    exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq (N * q) S E hE
  let e : Fin (Module.finrank ℚ̄ V) ≃ Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) := finCongr hn
  have hb₀ne : ∀ j, b₀ j ≠ 0 := fun j => hb₀li.ne_zero j
  have hmem : ∀ i, U * b₀ (e i) ∈ V := fun i => hV.ge (Submodule.mem_map_of_mem (hb₀V (e i)))
  refine ⟨fun i => U * b₀ (e i), hmem, ?_, fun i => ⟨?_, ?_⟩, fun i σ hσ => ?_⟩
  · have h1 : LinearIndependent ℚ̄ (LinearMap.mulLeft ℚ̄ U ∘ b₀) :=
      hb₀li.map' (LinearMap.mulLeft ℚ̄ U) (LinearMap.ker_eq_bot.mpr hinj)
    exact h1.comp e e.injective
  · have hne : U * b₀ (e i) ≠ 0 := mul_ne_zero hU0 (hb₀ne _)
    exact Gauss.exists_coeffMap_eq_smul_of_poles _ hne (fun W hW => hpJ (b₀ (e i)) (hb₀V _) (hb₀ne _) W hW)
  · have hne : U * b₀ (e i) ≠ 0 := mul_ne_zero hU0 (hb₀ne _)
    have hwne : w (U * b₀ (e i)) ≠ 0 := (map_ne_zero _).mpr hne
    refine Gauss.exists_coeffMap_eq_smul_of_poles _ hwne (fun W hW => ?_)
    rw [Gauss.ord_w] at hW
    rcases hpJq (b₀ (e i)) (hb₀V _) (hb₀ne _) _ hW with ⟨a, ha⟩ | h
    · left
      refine ⟨a, ?_⟩
      rw [← Gauss.ord_w, map_sub, Gauss.w_jQFun hqN, AlgEquiv.commutes] at ha
      exact ha
    · right
      exact (Gauss.isCusp_winv_smul_iff hqN data W).mp h
  · show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (U * b₀ (e i)) = U * b₀ (e i)
    rw [smul_mul', hUfix σ hσ, hb₀fix (e i) σ hσ]

set_option maxHeartbeats 6400000 in

private theorem Gauss.main_of_unit (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (S : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (E : Divisor ℚ̄ F) [FiniteDimensional ℚ̄ ↥(riemannRochSpace E)]
    (hE : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E)
    (U : F)
    (hU₁ : U ∈ R.R₁.integers) (hU₁u : IsUnit (⟨U, hU₁⟩ : R.R₁.integers))
    (hU₂ : U ∈ R.R₂.integers) (hU₂u : IsUnit (⟨U, hU₂⟩ : R.R₂.integers))
    (hUfix : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U)
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Gauss.IsCusp W)
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Gauss.IsCusp W) :
    ∃ (Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F)
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField A) (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) ∧
      ∀ j, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gf j = Gf j := by
  classical
  have hU0 : U ≠ 0 := fun h => hU₁u.ne_zero (Subtype.ext h)
  have hinj : Function.Injective (LinearMap.mulLeft ℚ̄ U) := by
    intro x y h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hU0 h
  have hn : Module.finrank ℚ̄ ↥((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))
      = Module.finrank ℚ̄ ↥(riemannRochSpace E) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (riemannRochSpace E))).symm
  obtain ⟨b, hbV, hbli, hbint, hbfix⟩ := Gauss.hint hqN data S E hE U hU0 hUfix hpJ hpJq
    ((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U)) rfl
  obtain ⟨G, hG₁, hG₂, hGV, hGli, hGfix⟩ :=
    exists_linearIndependent_residuePair_forall_arithmeticGalois_smul_eq_of_finiteDimensional_mul R.R₁ R.R₂
      R.residue₁_coeffMap R.mem_integers₂_iff R.residue₂_eq S
      ((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U)) ⟨b, hbV, hbli, hbint, hbfix⟩

  obtain ⟨u₁, hu₁⟩ := hU₁u
  obtain ⟨u₂, hu₂⟩ := hU₂u
  have hinv₁ : (((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) : F) = U⁻¹ := by
    rw [Gauss.coe_unit_inv, hu₁]
  have hinv₂ : (((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : F) = U⁻¹ := by
    rw [Gauss.coe_unit_inv, hu₂]

  let e : Fin (Module.finrank ℚ̄ ↥((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))) ≃
      Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) := finCongr hn
  set Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F := fun j => U⁻¹ * G (e.symm j) with hGf
  have hGf₁ : ∀ j, Gf j ∈ R.R₁.integers := fun j => by
    rw [hGf, ← hinv₁]; exact mul_mem (SetLike.coe_mem _) (hG₁ _)
  have hGf₂ : ∀ j, Gf j ∈ R.R₂.integers := fun j => by
    rw [hGf, ← hinv₂]; exact mul_mem (SetLike.coe_mem _) (hG₂ _)
  have hGfV : ∀ j, Gf j ∈ riemannRochSpace E := fun j => by
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp (hGV (e.symm j))
    rw [LinearMap.mulLeft_apply] at hfe
    have : Gf j = f := by
      rw [hGf]
      show U⁻¹ * G (e.symm j) = f
      rw [← hfe, ← mul_assoc, inv_mul_cancel₀ hU0, one_mul f]
    rw [this]; exact hf

  have ha₁ : R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) ≠ 0 :=
    R.R₁.residue_ne_zero_of_isUnit (Units.isUnit _)
  have ha₂ : R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) ≠ 0 :=
    R.R₂.residue_ne_zero_of_isUnit (Units.isUnit _)
  have hres₁ : ∀ j, R.R₁.residue ⟨Gf j, hGf₁ j⟩
      = R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * R.R₁.residue ⟨G (e.symm j), hG₁ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₁ j⟩ : R.R₁.integers)
        = ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * ⟨G (e.symm j), hG₁ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₁]
    rw [ex, map_mul]
  have hres₂ : ∀ j, R.R₂.residue ⟨Gf j, hGf₂ j⟩
      = R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * R.R₂.residue ⟨G (e.symm j), hG₂ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₂ j⟩ : R.R₂.integers)
        = ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * ⟨G (e.symm j), hG₂ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₂]
    rw [ex, map_mul]
  refine ⟨Gf, hGf₁, hGf₂, hGfV, ?_, fun j σ hσ => ?_⟩
  · have hfun : (fun j => (R.R₁.residue ⟨Gf j, hGf₁ j⟩, R.R₂.residue ⟨Gf j, hGf₂ j⟩))
        = fun j => (R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers)
            * ((fun i => (R.R₁.residue ⟨G i, hG₁ i⟩, R.R₂.residue ⟨G i, hG₂ i⟩)) (e.symm j)).1,
          R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers)
            * ((fun i => (R.R₁.residue ⟨G i, hG₁ i⟩, R.R₂.residue ⟨G i, hG₂ i⟩)) (e.symm j)).2) :=
      funext fun j => Prod.ext (hres₁ j) (hres₂ j)
    rw [hfun]
    exact Gauss.linearIndependent_mul_units (hGli.comp e.symm e.symm.injective) ha₁ ha₂
  · rw [hGf]
    show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (U⁻¹ * G (e.symm j)) = U⁻¹ * G (e.symm j)
    rw [smul_mul', Gauss.smul_inv_eq_of_smul_eq (hUfix σ hσ), hGfix (e.symm j) σ hσ]

private theorem Gauss.exists_linearIndependent_residuePair (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (S : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (E : Divisor ℚ̄ F)
    (hEfix : ∀ W ∈ E.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W = W)
    [FiniteDimensional ℚ̄ ↥(riemannRochSpace E)] :
    ∃ (Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F)
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField A) (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) ∧
      ∀ j, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gf j = Gf j := by
  have hE : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E :=
    fun σ hσ => Gauss.smul_divisor_eq_of_forall_mem_support fun W hW => hEfix W hW σ hσ
  obtain ⟨U, ⟨hU₁, hU₁u⟩, ⟨hU₂, hU₂u⟩, hpJ, hpJq, hUfix⟩ := Gauss.exists_bigU hqN R S E hEfix
  exact Gauss.main_of_unit hqN R S E hE U hU₁ hU₁u hU₂ hU₂u hUfix hpJ hpJq

end Pair

end ResiduePairLift

namespace ResiduePairLift
namespace Fibre

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section NodePairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def nodeCompatiblePairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) :
    Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _,
    fun i => ⟨0, ResiduePairLift.Eval.hasValue_zero _, ResiduePairLift.Eval.hasValue_zero _⟩⟩
  add_mem' := by
    rintro p p' ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    exact ⟨c + d, ResiduePairLift.Eval.hvAdd hc1 hd1, ResiduePairLift.Eval.hvAdd hc2 hd2⟩
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    exact ⟨a * c, ResiduePairLift.Eval.hvSmul a hc1, ResiduePairLift.Eval.hvSmul a hc2⟩

private theorem mem_nodeCompatiblePairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {p : F × F} :
    p ∈ nodeCompatiblePairs E₁ E₂ v₁ v₂ ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue p.1 c ∧ (v₂ i).HasValue p.2 c :=
  Iff.rfl

end NodePairs

section Descent

variable {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : F₀ →+* F) (hι : ∀ x : F₀, ((ι x : F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))

include hι in

private theorem map_algebraMap_eq (c : k₀) : ι (algebraMap k₀ F₀ c) = algebraMap k F (σ c) := by
  apply Subtype.ext
  rw [hι]
  change coeffMap σ (algebraMap k₀ (LaurentSeries k₀) c) = algebraMap k (LaurentSeries k) (σ c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

include hι in
private theorem mem_span_of_map_mem
    {n : ℕ} (r : Fin n → F₀ × F₀) (hr : LinearIndependent k₀ r)
    (T : Submodule k (F × F)) [FiniteDimensional k T]
    (hT : ∀ j, ((ι (r j).1 : F), (ι (r j).2 : F)) ∈ T) (hTn : Module.finrank k T ≤ n)
    (g : F₀ × F₀) (hg : ((ι g.1 : F), (ι g.2 : F)) ∈ T) :
    g ∈ Submodule.span k₀ (Set.range r) := by
  let φ : F₀ × F₀ → F × F := fun y => ((ι y.1 : F), (ι y.2 : F))
  have hpli : LinearIndependent k (φ ∘ r) := linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hr
  have hspan : Submodule.span k (Set.range (φ ∘ r)) = T := by
    refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨j, rfl⟩
      exact hT j
    · rw [finrank_span_eq_card hpli, Fintype.card_fin]
      exact hTn
  by_contra hnot
  have hli' : LinearIndependent k₀ (Fin.cons g r) := by
    first
      | exact linearIndependent_finCons.mpr ⟨hr, hnot⟩
      | exact linearIndependent_fin_cons.mpr ⟨hr, hnot⟩
  have himg : LinearIndependent k (φ ∘ Fin.cons g r) :=
    linearIndependent_map_prod_of_coe_eq_coeffMap σ F₀ F ι hι hli'
  rw [Fin.comp_cons] at himg
  first
    | (rw [linearIndependent_finCons, hspan] at himg; exact himg.2 hg)
    | (rw [linearIndependent_fin_cons, hspan] at himg; exact himg.2 hg)

end Descent

section Degrees

variable {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']

private theorem degree_mapDomain_of_deg_eq_one (r : Place K F → Place K' F')
    (h1 : ∀ w : Place K F, w.deg = 1) (h1' : ∀ v : Place K' F', v.deg = 1) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  classical
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index]
  · refine Finsupp.sum_congr fun w _ => ?_
    show D w * ((r w).deg : ℤ) = D w * (w.deg : ℤ)
    rw [h1, h1']
  · intro v; exact zero_mul _
  · intro v m n; exact add_mul _ _ _

private theorem degree_nonneg_of_deg_eq_one (h1 : ∀ w : Place K F, w.deg = 1) {D : Divisor K F} (hD : ∀ w, 0 ≤ D w) :
    0 ≤ Divisor.degree D := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun w _ => ?_
  show 0 ≤ D w * (w.deg : ℤ)
  rw [h1]; simpa using hD w

end Degrees

end ResiduePairLift.Fibre

namespace ResiduePairLift
namespace Fibre
open AlgebraicCurve

private theorem finsuppDegree_eq_divisorDegree {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h1 : ∀ w : Place K F, w.deg = 1) (E : Divisor K F) : Finsupp.degree E = Divisor.degree E := by
  classical
  simp only [Finsupp.degree, Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  show E w = E w * (w.deg : ℤ)
  rw [h1]; simp
end ResiduePairLift.Fibre

namespace ResiduePairLift
namespace Fibre

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem mapDomain_reduceFst_fstDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv
  have hW' : W ∈ (P.fstDiv D).support := hW
  unfold PlaceSpecialization.fstDiv at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictFst W := hW'.2
  exact h1.2 (hWv ▸ hv)

private theorem mapDomain_reduceSnd_sndDiv_eq_zero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finsupp.single_apply, if_neg]
  intro hWv
  have hW' : W ∈ (P.sndDiv D).support := hW
  unfold PlaceSpecialization.sndDiv at hW'
  rw [Finsupp.support_filter, Finset.mem_filter] at hW'
  have h1 : P.IsStrictSnd W := hW'.2
  exact h1.2 (hWv ▸ hv)

private theorem fstDiv_add_sndDiv (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) :
    P.fstDiv D + P.sndDiv D = D := by
  classical
  ext W
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h1 : P.IsStrictFst W
  · by_cases h2 : P.IsStrictSnd W
    · exfalso
      apply h1.2
      have e1 : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h1.1
      have e2 : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h2.1
      conv_rhs => rw [e2]
      rw [e1]
    · rw [if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : P.IsStrictSnd W
    · rw [if_neg h1, if_pos h2, zero_add]
    · rw [if_neg h1, if_neg h2, add_zero]
      by_contra h
      rcases hgood W (Finsupp.mem_support_iff.mpr (Ne.symm h)) with h' | h'
      · exact h1 h'
      · exact h2 h'

set_option maxHeartbeats 6400000 in

private theorem count (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))) :
    FiniteDimensional k ↥(nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D))
        (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
        (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))) ∧
      Module.finrank k ↥(nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D))
        (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
        (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))))
        ≤ Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) ∧
      FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := by
  classical
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  set E₁ := Finsupp.mapDomain P.reduceFst (P.fstDiv D) with hE₁
  set E₂ := Finsupp.mapDomain P.reduceSnd (P.sndDiv D) with hE₂
  set T := nodeCompatiblePairs E₁ E₂ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N)))
    (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) with hT

  have hgen : (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) : ℤ) + 1 = 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) + W.card := by
    exact_mod_cast genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q N hqN k W hW
  have hRR : ∀ Dk : Divisor k ↥(modularFunctionFieldC k N), 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤ Dk.degree →
      (Module.finrank k ↥(riemannRochSpace Dk) : ℤ) = Dk.degree + 1 - (genusFF k ↥(modularFunctionFieldC k N) : ℤ) := by
    have h := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC k N
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN] at h
    exact h
  have hRI := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace (N * q) D
  have hdegBar : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), w.deg = 1 := deg_eq_one_modularFunctionFieldBar (N * q)
  have hdegC : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := deg_eq_one_modularFunctionFieldC k N
  have hd₁ : Divisor.degree E₁ = Divisor.degree (P.fstDiv D) := degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hd₂ : Divisor.degree E₂ = Divisor.degree (P.sndDiv D) := degree_mapDomain_of_deg_eq_one _ hdegBar hdegC _
  have hsum : Divisor.degree (P.fstDiv D) + Divisor.degree (P.sndDiv D) = Divisor.degree D := by
    rw [← map_add, fstDiv_add_sndDiv P D hgood]

  set n : ℕ := W.card with hn
  have hcard : Fintype.card ↥W = n := Fintype.card_coe W
  have hfixW : ∀ w : ↥W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (w : Place k ↥(modularFunctionFieldC k N))) = w :=
    fun w => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr _ ((hW _).mp w.2)
  have hfixW' : ∀ w : ↥W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
      (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))) = arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)) :=
    fun w => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr _
      (arithFrobC_smul_mem_ssPlaces_univ q N k _ ((hW _).mp w.2))
  have hE₁0 : ∀ w : ↥W, E₁ (w : Place k ↥(modularFunctionFieldC k N)) = 0 := fun w => mapDomain_reduceFst_fstDiv_eq_zero P D (hfixW w)
  have hE₂0 : ∀ w : ↥W, E₂ (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) = 0 :=
    fun w => mapDomain_reduceSnd_sndDiv_eq_zero P D (hfixW' w)
  have ht₁ : ∀ w : ↥W, (1 : ↥(modularFunctionFieldC k N)) ≠ 0 ∧ (w : Place k ↥(modularFunctionFieldC k N)).ord (1 : ↥(modularFunctionFieldC k N)) = E₁ (w : Place k ↥(modularFunctionFieldC k N)) :=
    fun w => ⟨one_ne_zero, by rw [hE₁0]; exact (Place.hasValue_one _).ord_eq_zero one_ne_zero⟩
  have ht₂ : ∀ w : ↥W, (1 : ↥(modularFunctionFieldC k N)) ≠ 0 ∧
      (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))).ord (1 : ↥(modularFunctionFieldC k N)) = E₂ (arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) :=
    fun w => ⟨one_ne_zero, by rw [hE₂0]; exact (Place.hasValue_one _).ord_eq_zero one_ne_zero⟩

  have hfr₁ := hRR E₁ (by omega)
  have hfr₂ := hRR E₂ (by omega)
  have hD₂nn : ∀ V, 0 ≤ P.sndDiv D V := fun V => by
    unfold PlaceSpecialization.sndDiv; rw [Finsupp.filter_apply]; split_ifs
    · exact hD V
    · exact le_rfl
  have hd₂nn : 0 ≤ Divisor.degree (P.sndDiv D) := degree_nonneg_of_deg_eq_one hdegBar hD₂nn
  haveI hfin₁ : FiniteDimensional k ↥(riemannRochSpace E₁) := Module.finite_of_finrank_pos (by omega)
  haveI hfin₂ : FiniteDimensional k ↥(riemannRochSpace E₂) := Module.finite_of_finrank_pos (by omega)
  have hfin_of_le : ∀ Dk : Divisor k ↥(modularFunctionFieldC k N), Dk ≤ E₁ → FiniteDimensional k ↥(riemannRochSpace Dk) :=
    fun Dk hDk => Module.Finite.of_injective (Submodule.inclusion (ResiduePairLift.Eval.riemannRochSpace_mono hDk))
      (Submodule.inclusion_injective _)
  have hdegsum : ∀ (s : Finset ↥W), Divisor.degree (∑ j ∈ s, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ)) = s.card := by
    intro s
    rw [map_sum]
    simp only [Divisor.degree_single, hdegC, Nat.cast_one, mul_one, Finset.sum_const, nsmul_eq_mul]
  have hSnonneg : ∀ s : Finset ↥W, (0 : Divisor k ↥(modularFunctionFieldC k N)) ≤ ∑ j ∈ s, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ) :=
    fun s => Finset.sum_nonneg fun j _ => Finsupp.single_nonneg.mpr zero_le_one

  have hstep : ∀ i : ↥W,
      ∃ g ∈ riemannRochSpace (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) 1),
        g ∉ riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) 1) := by
    intro i
    have hn1 : 1 ≤ n := by
      rw [← hcard]; exact Fintype.card_pos_iff.mpr ⟨i⟩
    have hda : Divisor.degree (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))
        = Divisor.degree E₁ - (n - 1 : ℕ) := by
      rw [map_sub, hdegsum, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcard]
    have hdb : Divisor.degree (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ)) = Divisor.degree E₁ - n := by
      rw [map_sub, hdegsum, Finset.card_univ, hcard]
    have hra := hRR _ (by rw [hda]; push_cast; omega)
    have hrb := hRR _ (by rw [hdb]; omega)
    haveI : FiniteDimensional k ↥(riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) :=
      hfin_of_le _ (sub_le_self _ (hSnonneg _))
    apply ResiduePairLift.Eval.exists_mem_riemannRochSpace_not_mem_of_finrank_lt
    have : (Module.finrank k ↥(riemannRochSpace (E₁ - ∑ j : ↥W, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) : ℤ)
        < Module.finrank k ↥(riemannRochSpace (E₁ - ∑ j ∈ Finset.univ.erase i, Finsupp.single ((j : ↥W) : Place k ↥(modularFunctionFieldC k N)) (1 : ℤ))) := by
      rw [hra, hrb, hda, hdb]; push_cast; omega
    exact_mod_cast this

  have hsurj0 := AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
    E₁ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) Subtype.val_injective (fun _ => (1 : ↥(modularFunctionFieldC k N))) ht₁ hstep
  obtain ⟨hfinT, hcount⟩ :=
    AlgebraicCurve.finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
      E₁ E₂ (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N)))
      (fun _ => (1 : ↥(modularFunctionFieldC k N))) (fun _ => (1 : ↥(modularFunctionFieldC k N))) ht₁ ht₂ (fun _ => (1 : k)) hsurj0 T
      (fun p => by
        rw [hT, mem_nodeCompatiblePairs_iff]
        simp only [one_mul])
  rw [hcard] at hcount

  have hfinD : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := Module.finite_of_finrank_pos (by omega)
  refine ⟨hfinT, ?_, hfinD⟩
  have hc : (Module.finrank k ↥T : ℤ) + n ≤ (Module.finrank k ↥(riemannRochSpace E₁) : ℤ) + Module.finrank k ↥(riemannRochSpace E₂) := by
    exact_mod_cast hcount
  have : (Module.finrank k ↥T : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) := by
    rw [hfr₁, hfr₂] at hc
    omega
  exact_mod_cast this

end ResiduePairLift.Fibre

namespace ResiduePairLift
namespace Fibre

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem liesOverPrime {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) :
    A.LiesOverPrime q := by
  have h0 : R.redBar (IsLocalRing.residue A (q : A)) = 0 := by
    rw [R.redBar_residue, map_natCast, CharP.cast_eq_zero]
  have h1 : IsLocalRing.residue A (q : A) = 0 := R.redBar.injective (by rw [h0, map_zero])
  have h2 : (q : A) ∈ maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).mp h1
  have h3 : A.valuation ((q : A) : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff _).mp h2
  have e : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := map_natCast A.subtype q
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff, ← e]
  exact h3

private theorem main_family {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (Gf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D)) → ↥(modularFunctionFieldBar (N * q)))
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace D) ∧
      (∀ j, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Gf j = Gf j) ∧
      (g₁, g₂) ∈ Submodule.span (ResidueField A)
        (Set.range fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) := by
  classical

  obtain ⟨hfinT, hTn, hfd⟩ := count P hqN W hW D hD hgood hdeg₁ hdeg₂
  haveI := hfd

  obtain ⟨Gf, hG₁, hG₂, hGV, hGli, hGfix⟩ := Gauss.exists_linearIndependent_residuePair hqN R S D hDfix

  set r := fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩) with hr
  set φ : ↥(modularFunctionFieldFullC (ResidueField A) N) × ↥(modularFunctionFieldFullC (ResidueField A) N) →
      ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N) := fun y => ((R.ι y.1 : ↥(modularFunctionFieldC k N)), (R.ι y.2 : ↥(modularFunctionFieldC k N))) with hφ
  have hrli : LinearIndependent (ResidueField A) r := hGli

  set T : Submodule k (↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)) :=
    nodeCompatiblePairs (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) (Finsupp.mapDomain P.reduceSnd (P.sndDiv D))
      (fun w : ↥W => (w : Place k ↥(modularFunctionFieldC k N))) (fun w : ↥W => arithFrobC q k N • (w : Place k ↥(modularFunctionFieldC k N))) with hT
  have hpT : ∀ j, ((R.ι (r j).1 : ↥(modularFunctionFieldC k N)), (R.ι (r j).2 : ↥(modularFunctionFieldC k N))) ∈ T := fun j => by
    obtain ⟨h1, h2, h3⟩ :=
      ProlongationTuple.IsModel.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv hqN hW R hR hRL hNV hO
        D hD hgood (Gf j) (hGV j) (hG₁ j) (hG₂ j)
    exact ⟨h1, h2, fun w => h3 w w.2⟩
  have hgT : φ (g₁, g₂) ∈ T := by
    refine ⟨hg₁, hg₂, fun w => ?_⟩
    exact hnode (smulNodePair (arithFrobC q k N) (w : Place k ↥(modularFunctionFieldC k N)))
      (smulNodePair_mem_nodePairsOfPlaces _ w.2)

  haveI := hfinT
  have hgspan : (g₁, g₂) ∈ Submodule.span (ResidueField A) (Set.range r) :=
    mem_span_of_map_mem R.redBar _ _ R.ι R.ι_coe r hrli T hpT hTn (g₁, g₂) hgT
  exact ⟨Gf, hG₁, hG₂, hGV, hGfix, hgspan⟩

set_option maxHeartbeats 6400000 in

private theorem main {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ ∧
        ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • G = G := by
  classical
  obtain ⟨Gf, hG₁, hG₂, hGV, hGfix, hgspan⟩ :=
    main_family hqN hW R hR hRL hNV hO S D hD hgood hDfix hdeg₁ hdeg₂ g₁ g₂ hg₁ hg₂ hnode
  set r := fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩) with hr
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField A)).mp hgspan

  have hA : A.LiesOverPrime q := liesOverPrime R
  choose α hα hαfix using fun j =>
    ResiduePairLift.Inertia.exists_residue_eq_and_forall_inertia_apply_eq A (Fact.out : q.Prime) hA (μ j)
  have hcmem₁ : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    fun j => (R.R₁.algebraMap_mem_iff _).mpr (α j).2
  have hcmem₂ : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
    fun j => (R.R₂.algebraMap_mem_iff _).mpr (α j).2
  set cs₁ : _ → R.R₁.integers := fun j => ⟨_, hcmem₁ j⟩ with hcs₁
  set Gs₁ : _ → R.R₁.integers := fun j => ⟨Gf j, hG₁ j⟩ with hGs₁
  set cs₂ : _ → R.R₂.integers := fun j => ⟨_, hcmem₂ j⟩ with hcs₂
  set Gs₂ : _ → R.R₂.integers := fun j => ⟨Gf j, hG₂ j⟩ with hGs₂
  set x₁ : R.R₁.integers := ∑ j, cs₁ j * Gs₁ j with hx₁
  set x₂ : R.R₂.integers := ∑ j, cs₂ j * Gs₂ j with hx₂
  set G : ↥(modularFunctionFieldBar (N * q)) :=
    ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (α j : AlgebraicClosure ℚ) * Gf j with hGdef
  have hsum₁ : (x₁ : ↥(modularFunctionFieldBar (N * q))) = G := by
    have e : ((∑ j, cs₁ j * Gs₁ j : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q)))
        = ∑ j, ((cs₁ j * Gs₁ j : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₁, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
  have hsum₂ : (x₂ : ↥(modularFunctionFieldBar (N * q))) = G := by
    have e : ((∑ j, cs₂ j * Gs₂ j : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
        = ∑ j, ((cs₂ j * Gs₂ j : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₂, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
  have hterm₁ : ∀ j, R.R₁.residue (cs₁ j * Gs₁ j) = μ j • (r j).1 := by
    intro j
    have hc : R.R₁.residue (cs₁ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₁.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have hterm₂ : ∀ j, R.R₂.residue (cs₂ j * Gs₂ j) = μ j • (r j).2 := by
    intro j
    have hc : R.R₂.residue (cs₂ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₂.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have h₁ : G ∈ R.R₁.integers := by
    rw [← hsum₁]
    exact x₁.2
  have h₂ : G ∈ R.R₂.integers := by
    rw [← hsum₂]
    exact x₂.2
  have hGx₁ : (⟨G, h₁⟩ : R.R₁.integers) = x₁ := Subtype.ext hsum₁.symm
  have hGx₂ : (⟨G, h₂⟩ : R.R₂.integers) = x₂ := Subtype.ext hsum₂.symm
  refine ⟨G, h₁, h₂, ?_, ?_, ?_, ?_⟩
  · rw [hGdef]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hGV j)
  · rw [hGx₁, hx₁, map_sum, Finset.sum_congr rfl fun j _ => hterm₁ j]
    have h1 := congrArg Prod.fst hμ
    rw [Prod.fst_sum] at h1
    simpa only [Prod.smul_fst] using h1
  · rw [hGx₂, hx₂, map_sum, Finset.sum_congr rfl fun j _ => hterm₂ j]
    have h1 := congrArg Prod.snd hμ
    rw [Prod.snd_sum] at h1
    simpa only [Prod.smul_snd] using h1
  ·
    intro σ hσ
    rw [hGdef, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul', Gauss.galois_smul_algebraMap, hαfix j σ (hS σ hσ), hGfix j σ hσ]

end ResiduePairLift.Fibre

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree)
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree)
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ ∧
        ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • G = G := by
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hdegC : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := deg_eq_one_modularFunctionFieldC k N
  have hdeg₁' : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) := by
    first
      | exact hdeg₁
      | (rw [← ResiduePairLift.Fibre.finsuppDegree_eq_divisorDegree hdegC]; exact hdeg₁)
  have hdeg₂' : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) := by
    first
      | exact hdeg₂
      | (rw [← ResiduePairLift.Fibre.finsuppDegree_eq_divisorDegree hdegC]; exact hdeg₂)
  exact ResiduePairLift.Fibre.main hqN hW R hR hRL hNV hO S hS D hD hgood hDfix hdeg₁' hdeg₂' g₁ g₂ hg₁ hg₂ hnode

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv (solution)
