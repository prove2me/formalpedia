-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_fibreModel_cuspChart_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/de3ed358-0181-5f1a-bf4b-3da28aef2d29

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_CharPModel_exists_fibreModel_cuspChart
import Theorems.Thm_ModularCurve_CharPModel_exists_integral_lift_jChart_and_jInvChart
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationSubring
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental
import Theorems.Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.NumberTheory.Divisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_C qExpand_injective qExpand_qExpand jq jq_ne_zero jqN jqN_one dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin EvalSymm PhiIrreducible relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_phiIrreducible nonempty_modularPolynomialData transcendental_jq minpoly_jqN_eq_toAdjoin ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub ModularPolynomialData.evalSymm_of_prime"
namespace W3d11
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd.ModularCurve Polynomial"

section Generic

variable {R F : Type*} [CommRing R] [Field F]

private theorem eval₂_mem_valuationSubring (i : R →+* F) (V : ValuationSubring F) (hR : ∀ a : R, i a ∈ V)
    {y : F} (hy : y ∈ V) (c : R[X]) : c.eval₂ i y ∈ V := by
  refine Polynomial.induction_on' c (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [eval₂_add]
    exact add_mem hp hq
  · rw [eval₂_monomial]
    exact mul_mem (hR a) (pow_mem hy n)

private theorem mem_of_monic_root_of_mem (i : R →+* F) (x f : F) (p : R[X][X]) (hp : p.Monic)
    (hroot : p.eval₂ (eval₂RingHom i x) f = 0)
    (V : ValuationSubring F) (hR : ∀ a : R, i a ∈ V) (hx : x ∈ V) : f ∈ V := by
  set P : F[X] := p.map (eval₂RingHom i x) with hP
  have hPmonic : P.Monic := hp.map _
  have hProot : P.eval₂ (RingHom.id F) f = 0 := by
    rw [hP, eval₂_map, RingHom.id_comp]
    exact hroot
  have hPcoeff : ∀ j, P.coeff j ∈ V := by
    intro j
    rw [hP, coeff_map, coe_eval₂RingHom]
    exact eval₂_mem_valuationSubring i V hR hx _
  have hlifts : P ∈ Polynomial.lifts (algebraMap V F) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨P.coeff j, hPcoeff j⟩, rfl⟩
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := lifts_and_natDegree_eq_and_monic hlifts hPmonic
  have hint : IsIntegral V f := by
    refine ⟨Q', hQ'monic, ?_⟩
    rw [eval₂_eq_eval_map, hQ'map]
    rw [eval₂_eq_eval_map, Polynomial.map_id] at hProot
    exact hProot
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

private theorem mul_inv_pow_mem_of_monic_root (i : R →+* F) (x f : F) (m : ℕ) (p : R[X][X]) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom i x) f = 0)
    (V : ValuationSubring F) (hR : ∀ a : R, i a ∈ V) (hx : x ∉ V) :
    f * (x ^ m)⁻¹ ∈ V := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hx
  set n : ℕ := p.natDegree with hn
  set P : F[X] := p.map (eval₂RingHom i x) with hP
  have hPmonic : P.Monic := hp.map _
  have hPdeg : P.natDegree = n := hp.natDegree_map _
  have hProot : P.eval₂ (RingHom.id F) f = 0 := by
    rw [hP, eval₂_map, RingHom.id_comp]
    exact hroot
  set s : F := (x ^ m)⁻¹ with hs
  set Q : F[X] := P.scaleRoots s with hQ
  have hQmonic : Q.Monic := (monic_scaleRoots_iff s).mpr hPmonic
  have hQroot : Q.eval₂ (RingHom.id F) (s * f) = 0 := by
    have h := scaleRoots_eval₂_eq_zero (RingHom.id F) (s := s) hProot
    rw [RingHom.id_apply] at h
    exact h
  have hQcoeff : ∀ j, Q.coeff j ∈ V := by
    intro j
    rw [hQ, coeff_scaleRoots, hPdeg, hP, coeff_map, coe_eval₂RingHom]
    letI : Invertible x := invertibleOfNonzero hx0
    have key := eval₂_reflect_mul_pow i x ((n - j) * m) (p.coeff j) (hdeg j)
    rw [invOf_eq_inv] at key
    have hxpow : (x ^ ((n - j) * m)) ≠ 0 := pow_ne_zero _ hx0
    have e1 : (p.coeff j).eval₂ i x = (reflect ((n - j) * m) (p.coeff j)).eval₂ i x⁻¹ * x ^ ((n - j) * m) :=
      key.symm
    have e2 : s ^ (n - j) = (x ^ ((n - j) * m))⁻¹ := by
      rw [hs, inv_pow, ← pow_mul, mul_comm]
    rw [e1, e2, mul_assoc, mul_inv_cancel₀ hxpow, mul_one]
    exact eval₂_mem_valuationSubring i V hR hxinv _
  have hlifts : Q ∈ Polynomial.lifts (algebraMap V F) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨Q.coeff j, hQcoeff j⟩, rfl⟩
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := lifts_and_natDegree_eq_and_monic hlifts hQmonic
  have hint : IsIntegral V (s * f) := by
    refine ⟨Q', hQ'monic, ?_⟩
    rw [eval₂_eq_eval_map, hQ'map]
    rw [eval₂_eq_eval_map, Polynomial.map_id] at hQroot
    exact hQroot
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hmem : s * f ∈ V := by
    rw [← hy]
    exact y.2
  rw [mul_comm] at hmem
  exact hmem

end Generic

private theorem algebraMap_int_mem (V : ValuationSubring (LaurentSeries ℚ)) (a : ℤ) :
    algebraMap ℤ (LaurentSeries ℚ) a ∈ V := by
  rw [eq_intCast]
  exact intCast_mem V a

private theorem eval₂RingHom_eq_aeval (x : LaurentSeries ℚ) :
    eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) x = (aeval (R := ℤ) x).toRingHom :=
  RingHom.ext fun _ => rfl

private theorem jqN_prime_not_mem_of_jq_not_mem (p : ℕ) [Fact p.Prime]
    (V : ValuationSubring (LaurentSeries ℚ)) (h : jq ∉ V) : jqN p ∉ V := by
  intro hmem
  apply h
  obtain ⟨data⟩ := nonempty_modularPolynomialData p
  have hsymm : EvalSymm data.Φ := ModularPolynomialData.evalSymm_of_prime p data

  have hroot : data.Φ.eval₂ (eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) (jqN p)) jq = 0 := by
    rw [eval₂RingHom_eq_aeval, ← hsymm jq (jqN p)]
    exact data.eval_eq_zero
  exact mem_of_monic_root_of_mem (algebraMap ℤ (LaurentSeries ℚ)) (jqN p) jq data.Φ data.monic hroot V
    (algebraMap_int_mem V) hmem

private theorem C_prime (p : ℕ) [Fact p.Prime]
    (V : ValuationSubring (LaurentSeries ℚ)) (h : jq ∉ V) : jqN p * (jq ^ p)⁻¹ ∈ V := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData p
  have hsymm : EvalSymm data.Φ := ModularPolynomialData.evalSymm_of_prime p data
  have hbd := ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub p data hsymm
  have hdeg : ∀ j, (data.Φ.coeff j).natDegree ≤ (data.Φ.natDegree - j) * p := fun j => by
    rw [data.natDegree_eq, mul_comm]
    exact hbd j
  have hroot : data.Φ.eval₂ (eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) jq) (jqN p) = 0 := by
    rw [eval₂RingHom_eq_aeval]
    exact data.eval_eq_zero
  exact mul_inv_pow_mem_of_monic_root (algebraMap ℤ (LaurentSeries ℚ)) jq (jqN p) p data.Φ data.monic hdeg
    hroot V (algebraMap_int_mem V) h

private theorem qExpand_algebraMap (n : ℕ) [NeZero n] (a : ℚ) :
    qExpand ℚ n (algebraMap ℚ (LaurentSeries ℚ) a) = algebraMap ℚ (LaurentSeries ℚ) a := by
  have e : (qExpand ℚ n).comp (algebraMap ℚ (LaurentSeries ℚ)) = algebraMap ℚ (LaurentSeries ℚ) :=
    RingHom.ext_rat _ _
  exact RingHom.congr_fun e a

private theorem jqN_ne_zero' (p : ℕ) [NeZero p] : jqN p ≠ 0 := by
  unfold jqN
  intro h
  have : jq = 0 := qExpand_injective p (h.trans (map_zero _).symm)
  exact jq_ne_zero this

private theorem d11_C_jqN_aux :
    ∀ (N : ℕ), ∀ [NeZero N],
    ∀ (V : ValuationSubring (LaurentSeries ℚ)), (∀ a : ℚ, algebraMap ℚ _ a ∈ V) → jq ∉ V →
      jqN N * (jq ^ N)⁻¹ ∈ V := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro _ V hℚ h
    rcases eq_or_ne N 1 with hN1 | hN1
    · subst hN1
      rw [jqN_one, pow_one, mul_inv_cancel₀ jq_ne_zero]
      exact V.one_mem
    · obtain ⟨p, hp, M, hM⟩ := Nat.exists_prime_and_dvd hN1
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hM0 : M ≠ 0 := fun h0 => NeZero.ne N (by simp [hM, h0])
      haveI : NeZero M := ⟨hM0⟩
      have hMlt : M < N := by
        rw [hM]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hM0) hp.one_lt

      have hJ : jqN p ∉ V := jqN_prime_not_mem_of_jq_not_mem p V h

      let V' : ValuationSubring (LaurentSeries ℚ) := V.comap (qExpand ℚ p)
      have hℚ' : ∀ a : ℚ, algebraMap ℚ _ a ∈ V' := fun a => by
        show qExpand ℚ p (algebraMap ℚ _ a) ∈ V
        rw [qExpand_algebraMap p a]; exact hℚ a
      have hV' : jq ∉ V' := hJ

      have hIH := IH M hMlt V' hℚ' hV'

      subst hM

      have hT : jqN (p * M) * (jqN p ^ M)⁻¹ ∈ V := by
        have hmem : qExpand ℚ p (jqN M * (jq ^ M)⁻¹) ∈ V := hIH
        rw [map_mul, map_inv₀, map_pow] at hmem

        have e1 : qExpand ℚ p (jqN M) = jqN (p * M) := by
          show qExpand ℚ p (qExpand ℚ M jq) = qExpand ℚ (p * M) jq
          exact qExpand_qExpand M p jq
        have e2 : qExpand ℚ p jq = jqN p := rfl
        rw [e1, e2] at hmem
        exact hmem

      have hP : jqN p * (jq ^ p)⁻¹ ∈ V := C_prime p V h

      have hchain : jqN (p * M) * (jq ^ (p * M))⁻¹
          = (jqN (p * M) * (jqN p ^ M)⁻¹) * (jqN p * (jq ^ p)⁻¹) ^ M := by
        have hne : (jqN p : LaurentSeries ℚ) ^ M ≠ 0 := pow_ne_zero M (jqN_ne_zero' p)
        rw [mul_pow, inv_pow, pow_mul, mul_assoc (jqN (p * M)), inv_mul_cancel_left₀ hne]
      rw [hchain]
      exact mul_mem hT (pow_mem hP M)

private theorem d11_C_jqN (N : ℕ) [NeZero N]
    (V : ValuationSubring (LaurentSeries ℚ)) (hℚ : ∀ a : ℚ, algebraMap ℚ _ a ∈ V)
    (h : jq ∉ V) : jqN N * (jq ^ N)⁻¹ ∈ V :=
  d11_C_jqN_aux N V hℚ h

end ModularCurve.W3d11

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_C qExpand_injective qExpand_qExpand jq jq_ne_zero jqN jqN_one dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin EvalSymm PhiIrreducible relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_phiIrreducible nonempty_modularPolynomialData transcendental_jq minpoly_jqN_eq_toAdjoin ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub ModularPolynomialData.evalSymm_of_prime"
p2m_open "ModularCurve"
namespace W3D1

open Polynomial IntermediateField

private def jqR : (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) := ⟨jq, Algebra.subset_adjoin (Set.mem_singleton jq)⟩

private def evalAtJR : Polynomial ℤ →+* (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) :=
  Polynomial.eval₂RingHom (Int.castRingHom (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) jqR

private theorem algebraMap_comp_evalAtJR :
    (algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)).comp evalAtJR = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ) (evalAtJR Polynomial.X) = evalAtJ Polynomial.X
  rw [evalAtJ_X]
  show algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ) (Polynomial.eval₂ (Int.castRingHom (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) jqR Polynomial.X) = jq
  rw [Polynomial.eval₂_X]
  rfl

private def incRK : (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* ℚ⟮jq⟯ where
  toFun x := ⟨x.1, IntermediateField.algebra_adjoin_le_adjoin ℚ _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem algebraMap_comp_incRK :
    (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)).comp incRK
      = algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ) :=
  RingHom.ext fun _ => rfl

private theorem aeval_map_evalAtJR (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    Polynomial.aeval (jqN N) (data.Φ.map evalAtJR) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)).comp evalAtJR = evalAtJ from algebraMap_comp_evalAtJR]
  exact data.eval_eq_zero

private theorem isIntegral_adjoin_jqN (N : ℕ) [NeZero N] :
    IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  exact ⟨data.Φ.map evalAtJR, data.monic.map _, by
    simpa [Polynomial.aeval_def] using aeval_map_evalAtJR N data⟩

private theorem isIntegrallyClosed_Rj : IsIntegrallyClosed (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) :=
  Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental jq transcendental_jq

private theorem natDegree_minpoly_field (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
  rw [minpoly_jqN_eq_toAdjoin data hirr]
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

private theorem aeval_map_incRK_minpoly (N : ℕ) [NeZero N] :
    Polynomial.aeval (jqN N) ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    algebraMap_comp_incRK]
  exact minpoly.aeval (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)

private theorem natDegree_minpoly_adjoin_jqN (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    (minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).natDegree = dedekindPsi N := by
  haveI := isIntegrallyClosed_Rj
  have hint := isIntegral_adjoin_jqN N
  refine le_antisymm ?_ ?_
  ·
    have hdvd : minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) ∣ data.Φ.map evalAtJR :=
      minpoly.isIntegrallyClosed_dvd hint (aeval_map_evalAtJR N data)
    have h1 := Polynomial.natDegree_le_of_dvd hdvd (data.monic.map evalAtJR).ne_zero
    rwa [data.monic.natDegree_map evalAtJR, data.natDegree_eq] at h1
  ·
    have hdvd : minpoly ℚ⟮jq⟯ (jqN N) ∣ (minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK :=
      minpoly.dvd _ _ (aeval_map_incRK_minpoly N)
    have hμmonic : ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK).Monic :=
      (minpoly.monic hint).map _
    have h2 := Polynomial.natDegree_le_of_dvd hdvd hμmonic.ne_zero
    rwa [natDegree_minpoly_field N data hirr,
      (minpoly.monic hint).natDegree_map incRK] at h2

private theorem map_incRK_minpoly_eq (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    (minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK = data.toAdjoin := by
  haveI := isIntegrallyClosed_Rj
  have hint := isIntegral_adjoin_jqN N
  have hdvd : minpoly ℚ⟮jq⟯ (jqN N) ∣ (minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK :=
    minpoly.dvd _ _ (aeval_map_incRK_minpoly N)
  have hμmonic : ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK).Monic :=
    (minpoly.monic hint).map _
  obtain ⟨c, hc⟩ := hdvd
  have hdegs : ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map incRK).natDegree
      = (minpoly ℚ⟮jq⟯ (jqN N)).natDegree := by
    rw [(minpoly.monic hint).natDegree_map incRK, natDegree_minpoly_adjoin_jqN N data hirr,
      natDegree_minpoly_field N data hirr]
  have hKmonic : (minpoly ℚ⟮jq⟯ (jqN N)).Monic :=
    minpoly_jqN_eq_toAdjoin data hirr ▸ data.toAdjoin_monic

  have hcne : c ≠ 0 := by
    rintro rfl
    exact hμmonic.ne_zero (by simpa using hc)
  have hcdeg : c.natDegree = 0 := by
    have := hdegs
    rw [hc, Polynomial.natDegree_mul hKmonic.ne_zero hcne] at this
    omega
  have hcmonic : c.Monic := by
    have := hμmonic
    rw [hc] at this
    simpa [Polynomial.Monic, Polynomial.leadingCoeff_mul, hKmonic.leadingCoeff] using this
  have hc1 : c = 1 := by
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hcdeg
    have hc0 : c.coeff 0 = 1 := by
      have hlc := hcmonic
      rwa [Polynomial.Monic, Polynomial.leadingCoeff, hcdeg] at hlc
    rw [hC, hc0, map_one]
  rw [hc, hc1, mul_one, minpoly_jqN_eq_toAdjoin data hirr]

private theorem aeval_cast_coeff_eq (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) (i : ℕ) :
    Polynomial.aeval (jq : (LaurentSeries ℚ)) ((data.Φ.coeff i).map (Int.castRingHom ℚ)) =
      (((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).coeff i : (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) : (LaurentSeries ℚ)) := by

  have hL : Polynomial.aeval (jq : (LaurentSeries ℚ)) ((data.Φ.coeff i).map (Int.castRingHom ℚ))
      = evalAtJ (data.Φ.coeff i) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ) = algebraMap ℤ (LaurentSeries ℚ) from
        RingHom.ext_int _ _]
    rfl

  have hR : (((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).coeff i : (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) : (LaurentSeries ℚ))
      = evalAtJ (data.Φ.coeff i) := by
    have hcoeff : incRK ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).coeff i) = evalAtJGen (data.Φ.coeff i) := by
      have := congrArg (fun p => Polynomial.coeff p i) (map_incRK_minpoly_eq N data hirr)
      simpa [Polynomial.coeff_map, ModularPolynomialData.toAdjoin] using this
    calc (((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).coeff i : (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) : (LaurentSeries ℚ))
        = algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) (incRK ((minpoly (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).coeff i)) :=
          (RingHom.congr_fun algebraMap_comp_incRK _).symm
      _ = algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) (evalAtJGen (data.Φ.coeff i)) := by rw [hcoeff]
      _ = evalAtJ (data.Φ.coeff i) := by
          rw [← algebraMap_comp_evalAtJGen]; rfl
  rw [hL, hR]

private theorem exists_data_phiIrreducible_coeff_natDegree_le_of (N : ℕ) [NeZero N]
    (hD11 : ∀ V : ValuationSubring (LaurentSeries ℚ),
      (∀ a : ℚ, algebraMap ℚ (LaurentSeries ℚ) a ∈ V) → (jq : (LaurentSeries ℚ)) ∉ V →
        jqN N * ((jq : (LaurentSeries ℚ)) ^ N)⁻¹ ∈ V) :
    ∃ data : ModularPolynomialData N, PhiIrreducible data ∧
      ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by
  obtain ⟨data, hirr⟩ := exists_phiIrreducible N
  refine ⟨data, hirr, fun i => ?_⟩
  have hb := Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    (jq : (LaurentSeries ℚ)) transcendental_jq jq_ne_zero (jqN N) (isIntegral_adjoin_jqN N) N hD11 i
    ((data.Φ.coeff i).map (Int.castRingHom ℚ)) (aeval_cast_coeff_eq N data hirr i)
  rw [natDegree_minpoly_adjoin_jqN N data hirr] at hb
  have hdeg_eq : ((data.Φ.coeff i).map (Int.castRingHom ℚ)).natDegree
      = (data.Φ.coeff i).natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective (data.Φ.coeff i)
  rw [hdeg_eq] at hb
  exact hb.trans_eq (Nat.mul_comm _ _)

end W3D1
end ModularCurve

section Assembly

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd.ModularCurve.CharPModel ModularCurve.PhiGen AlgebraicCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_C qExpand_injective qExpand_qExpand jq jq_ne_zero jqN jqN_one dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin EvalSymm PhiIrreducible relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_phiIrreducible nonempty_modularPolynomialData transcendental_jq minpoly_jqN_eq_toAdjoin ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub ModularPolynomialData.evalSymm_of_prime"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "FibreModel exists_fibreModel_cuspChart exists_integral_lift_jChart_and_jInvChart"
namespace W3asm
p2m_open "ModularCurve.CharPModel ModularCurve"

private theorem exists_data_phiIrreducible_coeff_natDegree_le (N : ℕ) [NeZero N] :
    ∃ data : ModularPolynomialData N, PhiIrreducible data ∧
      ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) :=
  ModularCurve.W3D1.exists_data_phiIrreducible_coeff_natDegree_le_of N (ModularCurve.W3d11.d11_C_jqN N)

private theorem exists_fibreModel_cuspChart_of_not_dvd_w3
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] :
    ∃ fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A),
      fm.CuspChart := by
  have _ := hA
  obtain ⟨data, hirr, hdegX⟩ := exists_data_phiIrreducible_coeff_natDegree_le N
  have hred : Function.Surjective (IsLocalRing.residue ↥A) := Ideal.Quotient.mk_surjective
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi (ResidueField ↥A) N ℓ hℓN
  have hlift := exists_integral_lift_jChart_and_jInvChart N A ℓ hℓN (ResidueField ↥A)
    (IsLocalRing.residue ↥A) hred
  exact exists_fibreModel_cuspChart N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) hred data hdeg hdegX
    hlift.1 hlift.2

end ModularCurve.CharPModel.W3asm

end Assembly

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd.ModularCurve.CharPModel AlgebraicCurve IsLocalRing in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] :
    ∃ fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A),
      fm.CuspChart :=
  ModularCurve.CharPModel.W3asm.exists_fibreModel_cuspChart_of_not_dvd_w3 N ℓ hℓN A hA

end

end S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd (solution)
