-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cf472f95-f07a-5822-94c3-b62214e75289

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_IncidenceSystem
import Definitions.Def_MDivRepresents
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mDivRepresents
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.symPoly_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace SeamTwo

open MvPolynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem not_strict_both (P : PlaceSpecialization A q N data hKr k red hα hβ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (h1 : P.IsStrictFst V) (h2 : P.IsStrictSnd V) : False := by
  obtain ⟨hφ, hne⟩ := h1
  obtain ⟨hψ, -⟩ := h2
  exact hne (by rw [hφ, ← hψ])

theorem div_apply_fst (P : PlaceSpecialization A q N data hKr k red hα hβ) {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (i₁ : Fin d₁) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.IsStrictFst V) (hVr : P.reduceFst V = P.reduceFst (Q₁ i₁)) :
    ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
      = (Finsupp.single (Q₁' i₁) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V := by
  classical
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
  have h2 : ∑ j, (Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hj
    have hs : P.IsStrictSnd V := by rw [← hj]; exact hQ₂' j
    exact not_strict_both P V hV hs
  rw [h2, add_zero, Finset.sum_eq_single i₁]
  · intro i _ hi
    rw [Finsupp.single_apply, if_neg]
    intro hiV
    refine hi (hinj₁ ?_)
    show P.reduceFst (Q₁ i) = P.reduceFst (Q₁ i₁)
    have hx : P.reduceFst (Q₁' i) = P.reduceFst V := by rw [hiV]
    rw [← hred₁ i, hx, hVr]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem div_apply_snd (P : PlaceSpecialization A q N data hKr k red hα hβ) {d₁ d₂ : ℕ}
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (i₂ : Fin d₂) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.IsStrictSnd V) (hVr : P.reduceSnd V = P.reduceSnd (Q₂ i₂)) :
    ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
      = (Finsupp.single (Q₂' i₂) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V := by
  classical
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
  have h1 : ∑ i, (Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hi
    have hs : P.IsStrictFst V := by rw [← hi]; exact hQ₁' i
    exact not_strict_both P V hs hV
  rw [h1, zero_add, Finset.sum_eq_single i₂]
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro hjV
    refine hj (hinj₂ ?_)
    show P.reduceSnd (Q₂ j) = P.reduceSnd (Q₂ i₂)
    have hx : P.reduceSnd (Q₂' j) = P.reduceSnd V := by rw [hjV]
    rw [← hred₂ j, hx, hVr]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem evalBar_pinned (N q : ℕ) [NeZero N] [Fact q.Prime] (c : Option (Fin 2) → ↥(modularFunctionFieldBar (N * q))) (u τ : A) (m' : ℕ) :
    PlaceSpecialization.evalBar N q c ((X none - C u) ^ m' * (X none - C τ) : MvPolynomial (Option (Fin 2)) A)
      = (c none - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) ^ m' * (c none - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) := by
  unfold PlaceSpecialization.evalBar
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C, RingHom.comp_apply]
  rfl

theorem evalBar_one (N q : ℕ) [NeZero N] [Fact q.Prime] (c : Option (Fin 2) → ↥(modularFunctionFieldBar (N * q))) :
    PlaceSpecialization.evalBar N q c (1 : MvPolynomial (Option (Fin 2)) A) = 1 := by
  unfold PlaceSpecialization.evalBar
  exact MvPolynomial.eval₂_one _ _

theorem coeff_pinned_mem {A' : Type*} [CommRing A'] (I : Ideal A') (u τ : A') (huτ : u - τ ∈ I) (m' : ℕ)
    (r : Fin (m' + 1)) :
    (((Polynomial.C u + Polynomial.X - Polynomial.C u) ^ m' * (Polynomial.C u + Polynomial.X - Polynomial.C τ)
        : Polynomial A').coeff r) ∈ I := by
  rw [add_sub_cancel_left,
    show (Polynomial.C u + Polynomial.X - Polynomial.C τ : Polynomial A') = Polynomial.X + Polynomial.C (u - τ) by
      rw [map_sub]; ring,
    mul_add, ← pow_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
  have hr : (r : ℕ) ≠ m' + 1 := by have := r.2; omega
  rw [if_neg hr, zero_add]
  split_ifs with h1 h2
  · exact huτ
  · exact I.zero_mem
  · exact I.zero_mem

theorem spoly_single_eq_one {A' : Type*} [CommRing A'] (m' : ℕ) :
    (∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) ((Pi.single 0 1 : Fin (m' + 1) → A') r')) = (1 : Polynomial A') := by
  rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
  · simp
  · intro r' _ hr'; rw [Pi.single_eq_of_ne hr', map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end SeamTwo

open MvPolynomial IncidenceSystem in

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
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m' : ℕ) (hm : ((m' + 1 : ℕ) : k) ≠ 0) :
    ∃ (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q)))
      (hh₁ : ∀ l, h l ∈ R.R₁.integers) (hh₂ : ∀ l, h l ∈ R.R₂.integers)
      (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A),
      h 0 = 1 ∧
      (∀ l, h l ≠ 0) ∧
      (∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
          + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l)) ∧
      (∀ l,
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)) c)) ∧
      LinearIndependent k (fun l =>
        ((R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)))) ∧
      P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt := by
  classical

  have hred : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := fun a => by
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

  obtain ⟨h', h₁', h₂', hh0', hne', hL', hland', hind'⟩ :=
    ProlongationTuple.IsModel.exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul hqN hW R hR hRL hNV hO
      Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hT₁sm hT₂sm hgp₁ hgp₂ hdeg Q₁' Q₂' hQ₁' hQ₂' hred₁ hred₂
      Qs hQs hQs' (m' + 1) hm
  have hidx : (m' + 1) * (d₁ + d₂) - (d₁ + d₂) + 1 = (d₁ + d₂) * m' + 1 := by
    rw [Nat.add_mul, one_mul, Nat.add_sub_cancel, Nat.mul_comm]
  set e : Fin ((d₁ + d₂) * m' + 1) → Fin ((m' + 1) * (d₁ + d₂) - (d₁ + d₂) + 1) := Fin.cast hidx.symm with he
  set h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q)) := fun l => h' (e l) with hh
  have hh₁ : ∀ l, h l ∈ R.R₁.integers := fun l => h₁' (e l)
  have hh₂ : ∀ l, h l ∈ R.R₂.integers := fun l => h₂' (e l)
  have hm1 : ((m' + 1 : ℕ) : ℤ) - 1 = (m' : ℤ) := by push_cast; ring
  have hhL : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
        + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (h l) := by
    intro l V
    have := hL' (e l) V
    rw [hm1] at this
    exact this

  have perPoint : ∀ i : Fin (d₁ + d₂), ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin ((d₁ + d₂) * m') → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin ((d₁ + d₂) * m') → Fin (m' + 1) → A),
      Sum.elim (fun i₁ => PlaceSpecialization.IsFstTriple (q := q) (P.reduceFst (Q₁ i₁)) (red u) z y₁ y₂)
          (fun i₂ => PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd (Q₂ i₂)) (red u) z y₁ y₂) (finSumFinEquiv.symm i) ∧
      (∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (G 0).vars ∧
      0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) ∧
      (∀ j : Fin 2, 0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord
        (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j 0 : (AlgebraicClosure ℚ)))) ∧
      0 < (Sum.elim Q₁' Q₂' (finSumFinEquiv.symm i)).ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) ∧
      red τ = red u ∧
      (∀ l, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (p l) =
        h l.succ * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : (AlgebraicClosure ℚ))) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : (AlgebraicClosure ℚ))) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (s l)) ∧
      (∀ l, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) (s l)) ≠ 0) ∧
      (∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0))
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) ∧
      (∀ (j : Fin 2) (r : Fin (m' + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0) ∧
      (∀ (l : Fin ((d₁ + d₂) * m')) (r : Fin (m' + 1)),
        ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ l r')) *
            MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0) := by
    intro i
    obtain ⟨si, rfl⟩ : ∃ si, finSumFinEquiv si = i := ⟨_, Equiv.apply_symm_apply _ _⟩
    rcases si with i₁ | i₂
    · simp only [Equiv.symm_apply_apply, Sum.elim_inl]
      have hv : P.reduceFst (Q₁ i₁) ∈ T₁ := (hT₁ _).mpr ⟨i₁, rfl⟩
      exact ProlongationTuple.IsModel.exists_chartData_of_isStrictFst P hqN hW R hR hRL hNV hO (Q₁ i₁) (Q₁' i₁)
        (hQ₁ i₁) (hQ₁' i₁) (hred₁ i₁) (hT₁aff _ hv) (hT₁sm _ hv) (hT₁gen i₁) m' (fun l => h l.succ)
        (fun l => hh₁ l.succ) (fun l V hV hVr => by
          have hb := hhL l.succ V
          rw [SeamTwo.div_apply_fst P Q₁ Q₁' Q₂' hQ₂' hinj₁ hred₁ i₁ V hV hVr,
            SeamTwo.div_apply_fst P Q₁ Q₁ Q₂ hQ₂ hinj₁ (fun _ => rfl) i₁ V hV hVr] at hb
          exact hb)
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr]
      have hv : P.reduceSnd (Q₂ i₂) ∈ T₂ := (hT₂ _).mpr ⟨i₂, rfl⟩
      exact ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd P hqN hW R hR hRL hNV hO (Q₂ i₂) (Q₂' i₂)
        (hQ₂ i₂) (hQ₂' i₂) (hred₂ i₂) (hT₂aff _ hv) (hT₂sm _ hv) (hT₂gen i₂) m' (fun l => h l.succ)
        (fun l => hh₂ l.succ) (fun l V hV hVr => by
          have hb := hhL l.succ V
          rw [SeamTwo.div_apply_snd P Q₁' Q₂ Q₂' hQ₁' hinj₂ hred₂ i₂ V hV hVr,
            SeamTwo.div_apply_snd P Q₁ Q₂ Q₂ hQ₁ hinj₂ (fun _ => rfl) i₂ V hV hVr] at hb
          exact hb)
  choose z y₁ y₂ u τ w G p s σ ha hb hvars hc1 hc2 hc3 hτu hd he hf hbr hinv using perPoint

  let Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A :=
    { G := G
      p := fun kk i => Option.elim kk ((X none - C (u i)) ^ m' * (X none - C (τ i))) (fun l => p i l)
      s := fun kk i => Option.elim kk 1 (fun l => s i l)
      u₀ := u
      w₀ := w
      σ₀ := fun kk i => Option.elim kk (Pi.single 0 1) (fun l => σ i l) }
  have huτ : ∀ i, u i - τ i ∈ IsLocalRing.maximalIdeal A := fun i => by
    rw [← hred, map_sub, hτu, sub_self]

  have hsubst : ∀ i, IncidenceSystem.substAt Dt.centre i (Dt.p none i)
      = (Polynomial.C (u i) + Polynomial.X - Polynomial.C (u i)) ^ m'
          * (Polynomial.C (u i) + Polynomial.X - Polynomial.C (τ i)) := by
    intro i
    show MvPolynomial.aeval (IncidenceSystem.coordAt Dt.centre i) ((X none - C (u i)) ^ m' * (X none - C (τ i))) = _
    simp only [map_mul, map_pow, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
    rfl
  have hspoly : ∀ i, IncidenceSystem.spoly Dt.centre none i = 1 := fun i => SeamTwo.spoly_single_eq_one m'
  have hinc : ∀ i (r : Fin (m' + 1)), MvPolynomial.eval Dt.centre (Dt.inc i r) ∈ IsLocalRing.maximalIdeal A := by
    intro i r
    rw [IncidenceSystem.eval_inc]
    have hc0 : ∀ kk, Dt.centre (Var.c kk) = 0 := fun _ => rfl
    simp only [hc0, zero_mul, Finset.sum_const_zero, add_zero]
    rw [hsubst, hspoly, mul_one]
    exact SeamTwo.coeff_pinned_mem _ _ _ (huτ i) m' r
  refine ⟨h, hh₁, hh₂, Dt, ?_, fun l => hne' (e l), hhL, fun l => hland' (e l), ?_, ?_, ?_⟩
  · show h' (e 0) = 1
    rw [show e 0 = 0 from Fin.ext rfl]
    exact hh0'
  · exact hind'.comp e (Fin.cast_injective _)
  ·
    intro i
    refine ⟨z i, y₁ i, y₂ i, τ i, ha i, hb i, hvars i, hc1 i, hc2 i, hc3 i, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · intro kk
      rcases kk with _ | l
      · change PlaceSpecialization.evalBar N q (fun o => Option.elim o (z i) ![y₁ i, y₂ i])
            ((X none - C (u i)) ^ m' * (X none - C (τ i)))
          = (1 : ↥(modularFunctionFieldBar (N * q))) * (z i - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u i : (AlgebraicClosure ℚ))) ^ m'
            * (z i - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ i : (AlgebraicClosure ℚ)))
            * PlaceSpecialization.evalBar N q (fun o => Option.elim o (z i) ![y₁ i, y₂ i]) 1
        rw [SeamTwo.evalBar_pinned, SeamTwo.evalBar_one, one_mul, mul_one]
        rfl
      · exact hd i l
    · intro kk
      rcases kk with _ | l
      · show red (MvPolynomial.eval _ (1 : MvPolynomial (Option (Fin 2)) A)) ≠ 0
        rw [map_one, map_one]
        exact one_ne_zero
      · exact he i l
    · intro j
      exact hf i j
  ·
    intro v
    rcases v with i | ⟨i, j, r⟩ | ⟨kk, i, r⟩ | kk
    · exact hinc i (Fin.last m')
    · rw [show Dt.system (Var.w i j r) = Dt.branch i j r from rfl, IncidenceSystem.eval_branch]
      rw [show IncidenceSystem.substAt Dt.centre i (Dt.G i j) = MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C (u i) + Polynomial.X)
              (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w i j r'))) (G i j) from rfl, hbr i j r]
      exact zero_mem _
    · rw [show Dt.system (Var.σ kk i r) = Dt.inv kk i r from rfl, IncidenceSystem.eval_inv]
      rcases kk with _ | l
      · rw [hspoly, show Dt.s none i = 1 from rfl, show IncidenceSystem.substAt Dt.centre i 1 = 1 from map_one _,
          mul_one, sub_self, Polynomial.coeff_zero]
        exact zero_mem _
      · rw [show IncidenceSystem.spoly Dt.centre (some l) i * IncidenceSystem.substAt Dt.centre i (Dt.s (some l) i) - 1
            = (∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ i l r')) *
              MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C (u i) + Polynomial.X)
              (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w i j r'))) (s i l) - 1 from rfl, hinv i l r]
        exact zero_mem _
    · exact hinc _ _

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mDivRepresents
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mDivRepresents (solution)
