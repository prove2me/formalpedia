-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/32208e16-2050-59e2-b544-ba389deb4fce

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_hasValue_smul_of_generalPosition
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
import Theorems.Thm_ModularCurve_exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.symPoly_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.IsModel modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence smulNodePair nodePairsOfPlaces smulNodePair_mem_nodePairsOfPlaces ssPlaces IsAffineGeomPlace arithFrobC deg_eq_one_modularFunctionFieldBar exists_eq_algebraMap_of_hasValue_smul_of_generalPosition exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.IsModel reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne.ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

private theorem _root_.ModularCurve.PlaceSpecialization.not_isStrictFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h2 : P.IsStrictSnd W) : ¬ P.IsStrictFst W := by
  intro h1
  apply h1.2
  rw [h1.1, ← h2.1]

p2m_export "ModularCurve.PlaceSpecialization" "not_isStrictFst_of_isStrictSnd"

theorem degree_eq_sum (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    D.degree = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun W _ => ?_
  simp [ModularCurve.deg_eq_one_modularFunctionFieldBar]

private theorem _root_.ModularCurve.PlaceSpecialization.fstDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hE : 0 ≤ E) :
    0 ≤ P.fstDiv E := by
  intro W
  simp only [fstDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

p2m_export "ModularCurve.PlaceSpecialization" "fstDiv_nonneg"
private theorem _root_.ModularCurve.PlaceSpecialization.sndDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hE : 0 ≤ E) :
    0 ≤ P.sndDiv E := by
  intro W
  simp only [sndDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

p2m_export "ModularCurve.PlaceSpecialization" "sndDiv_nonneg"

private theorem _root_.ModularCurve.PlaceSpecialization.exists_eq_fstDiv_add_sndDiv_add {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hE : 0 ≤ E) :
    ∃ E₃ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), 0 ≤ E₃ ∧
      E = P.fstDiv E + P.sndDiv E + E₃ ∧ ∀ W ∈ E₃.support, ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W := by
  classical
  refine ⟨(E.filter fun W => ¬ P.IsStrictFst W).filter fun W => ¬ P.IsStrictSnd W, ?_, ?_, ?_⟩
  · intro W
    simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs <;> first | exact hE W | exact le_rfl
  · ext W
    simp only [fstDiv, sndDiv, Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
    by_cases h1 : P.IsStrictFst W
    · have h2 : ¬ P.IsStrictSnd W := fun h2 => P.not_isStrictFst_of_isStrictSnd h2 h1
      simp [h1, h2]
    · by_cases h2 : P.IsStrictSnd W
      · simp [h1, h2]
      · simp [h1, h2]
  · intro W hW
    rw [Finsupp.mem_support_iff] at hW
    simp only [Finsupp.filter_apply] at hW
    by_cases h2 : ¬ P.IsStrictSnd W
    · rw [if_pos h2] at hW
      by_cases h1 : ¬ P.IsStrictFst W
      · exact ⟨h1, h2⟩
      · rw [if_neg h1] at hW; exact absurd rfl hW
    · rw [if_neg h2] at hW; exact absurd rfl hW

p2m_export "ModularCurve.PlaceSpecialization" "exists_eq_fstDiv_add_sndDiv_add"

private theorem _root_.ModularCurve.PlaceSpecialization.exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE : 0 ≤ E)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (h₁ : Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ))
    (h₂ : Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ))
    (hdeg : E.degree = (d₁ + d₂ : ℕ)) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      E = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) := by
  classical
  obtain ⟨Q₁', hE₁, hred₁⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single P.reduceFst (P.fstDiv E)
    (P.fstDiv_nonneg hE) (fun i => P.reduceFst (Q₁ i)) hinj₁ h₁
  obtain ⟨Q₂', hE₂, hred₂⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single P.reduceSnd (P.sndDiv E)
    (P.sndDiv_nonneg hE) (fun j => P.reduceSnd (Q₂ j)) hinj₂ h₂

  have mem₁ : ∀ i, Q₁' i ∈ (P.fstDiv E).support := by
    intro i
    rw [hE₁, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro j _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨i, Finset.mem_univ _, by simp⟩
  have mem₂ : ∀ j, Q₂' j ∈ (P.sndDiv E).support := by
    intro j
    rw [hE₂, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨j, Finset.mem_univ _, by simp⟩
  have hQ₁' : ∀ i, P.IsStrictFst (Q₁' i) := fun i => by
    have := mem₁ i
    rw [fstDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  have hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j) := fun j => by
    have := mem₂ j
    rw [sndDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  refine ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, ?_⟩

  obtain ⟨E₃, hE₃, hsplit, -⟩ := P.exists_eq_fstDiv_add_sndDiv_add hE
  have hmass : E₃.sum (fun _ n => n) = 0 := by
    have h := congrArg (fun D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) =>
      D.sum (fun _ n => n)) hsplit
    beta_reduce at h
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← degree_eq_sum, hdeg, hE₁, hE₂,
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl),
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)] at h
    simp only [Finsupp.sum_single_index, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, mul_one] at h
    push_cast at h
    omega
  have hE₃0 : E₃ = 0 := by
    by_contra hne
    obtain ⟨W, hW⟩ : ∃ W, E₃ W ≠ 0 := by
      by_contra h'; push Not at h'; exact hne (Finsupp.ext h')
    have hpos : 0 < E₃.sum (fun _ n => n) := by
      rw [Finsupp.sum]
      exact Finset.sum_pos' (fun b _ => hE₃ b)
        ⟨W, Finsupp.mem_support_iff.mpr hW, lt_of_le_of_ne (hE₃ W) (Ne.symm hW)⟩
    omega
  rw [hsplit, hE₃0, add_zero, hE₁, hE₂]

p2m_export "ModularCurve.PlaceSpecialization" "exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv"
end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.IsModel modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence smulNodePair nodePairsOfPlaces smulNodePair_mem_nodePairsOfPlaces ssPlaces IsAffineGeomPlace arithFrobC deg_eq_one_modularFunctionFieldBar exists_eq_algebraMap_of_hasValue_smul_of_generalPosition exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.IsModel reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue₁ residue₂ residue₁_apply residue₂_apply OrderLawFixed IsModel NodeValueLaw RegularityLaw R₁ mk ι R₂ sectionPair_bounds_of_regularityLaw_of_isModel_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne.ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem exists_smul_mem_integers_both (R : P.ProlongationTuple)
    {f : ↥(modularFunctionFieldBar (1 * q))} (hf : f ≠ 0) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R.R₁.integers) (h₂ : c • f ∈ R.R₂.integers),
      R.R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R.R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  obtain ⟨c₁, hc₁, hr₁⟩ := R.R₁.exists_smul_mem f hf
  obtain ⟨c₂, hc₂, hr₂⟩ := R.R₂.exists_smul_mem f hf
  have hc₁0 : c₁ ≠ 0 := R.R₁.smul_const_ne_zero hc₁ hr₁
  have hc₂0 : c₂ ≠ 0 := R.R₂.smul_const_ne_zero hc₂ hr₂
  rcases A.mem_or_inv_mem (c₁ / c₂) with h | h
  · have hmem : c₁ • f ∈ R.R₂.integers := by
      have e : c₁ • f = algebraMap (AlgebraicClosure ℚ) _ (c₁ / c₂) * (c₂ • f) := by
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₂0]
      rw [e]
      exact mul_mem ((R.R₂.algebraMap_mem_iff _).mpr h) hc₂
    exact ⟨c₁, hc₁0, hc₁, hmem, Or.inl hr₁⟩
  · have hmem : c₂ • f ∈ R.R₁.integers := by
      have e : c₂ • f = algebraMap (AlgebraicClosure ℚ) _ (c₂ / c₁) * (c₁ • f) := by
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₁0]
      rw [inv_div] at h
      rw [e]
      exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr h) hc₁
    exact ⟨c₂, hc₂0, hmem, hc₂, Or.inr hr₂⟩

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (g : α → β) (D : α →₀ ℤ) (v : β) :
    Finsupp.mapDomain g D v = ∑ W ∈ D.support, if g W = v then D W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

set_option maxHeartbeats 12800000 in

theorem mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ 1)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)

    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : 0 ≤ E)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hDgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D, hadm⟩ = 0)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord f) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) ∧
    Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by
  classical
  set φ := frobOnPlacesGeomLevel k 1 data hKr with hφ

  have hgp : GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q k 1) W)
      (P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D) :=
    (GluedPic0.mk_eq_zero_iff (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨_, hadm⟩).mp hmk
  obtain ⟨hb₁, hb₂, av, bv, hb₁0, hb₂0, hdiv₁, hdiv₂, hvals, hratio⟩ := hgp
  have hab : ∀ s, av s = bv s := by
    intro s
    have h0 : (P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D).2.2 = 0 := rfl
    rw [h0] at hratio
    have hs := congrFun hratio s
    simp only [Pi.zero_apply] at hs
    have : av s / bv s = 1 := ofMul_eq_zero.mp hs.symm
    exact div_eq_one.mp this
  have hvalsW : ∀ w ∈ W, ∃ c : k, c ≠ 0 ∧ w.HasValue hb₁ c ∧ (arithFrobC q k 1 • w).HasValue hb₂ c := by
    intro w hw
    let s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) :=
      ⟨smulNodePair (arithFrobC q k 1) w, smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k 1) hw⟩
    refine ⟨av s, (av s).ne_zero, (hvals s).1, ?_⟩
    rw [hab s]
    exact (hvals s).2
  have hdiv₁' : ∀ v, Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = v.ord hb₁ := hdiv₁
  have hdiv₂' : ∀ v, Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = v.ord hb₂ := hdiv₂

  obtain ⟨c, hc0, hG₁, hG₂, hres⟩ := exists_smul_mem_integers_both R hf0
  have hdivG : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
        - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord (c • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_mul ((map_ne_zero _).mpr hc0) hf0,
      (V.hasValue_algebraMap c).ord_eq_zero hc0, zero_add]

  obtain ⟨hA₁, hB₁, hA₂, hB₂, hC⟩ := sectionPair_bounds_of_regularityLaw_of_isModel_levelOne hR hW hRL Q₁ Q₂ hQ₁ hQ₂
    hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff E D hE0 hDgood (c • f) hG₁ hG₂ hdivG hb₁ hb₂ hb₁0 hb₂0
    hdiv₁' hdiv₂' hvalsW
  set u₁ : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨c • f, hG₁⟩ * hb₁ with hu₁
  set u₂ : ↥(modularFunctionFieldC k 1) := R.residue₂ ⟨c • f, hG₂⟩ * hb₂ with hu₂
  obtain ⟨c', hu₁c, hu₂c⟩ := ModularCurve.exists_eq_algebraMap_of_hasValue_smul_of_generalPosition (arithFrobC q k 1) W T₁ T₂
    hgp₁ hgp₂ u₁ u₂ hA₁ hB₁ hA₂ hB₂ hC
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hu₁c hu₂c
    rcases hres with h | h
    · apply h
      have : R.residue₁ ⟨c • f, hG₁⟩ = 0 := by
        rcases mul_eq_zero.mp hu₁c with h' | h'
        · exact h'
        · exact absurd h' hb₁0
      simpa [residue₁_apply] using this
    · apply h
      have : R.residue₂ ⟨c • f, hG₂⟩ = 0 := by
        rcases mul_eq_zero.mp hu₂c with h' | h'
        · exact h'
        · exact absurd h' hb₂0
      simpa [residue₂_apply] using this
  have hinjι : Function.Injective R.ι := R.ι.injective
  have hres₁ : R.R₁.residue ⟨c • f, hG₁⟩ ≠ 0 := by
    intro h; apply hc'0
    have : u₁ = 0 := by rw [hu₁, residue₁_apply, h, map_zero, zero_mul]
    rw [this] at hu₁c
    exact ((map_eq_zero_iff _ (algebraMap k ↥(modularFunctionFieldC k 1)).injective).mp hu₁c.symm)
  have hres₂ : R.R₂.residue ⟨c • f, hG₂⟩ ≠ 0 := by
    intro h; apply hc'0
    have : u₂ = 0 := by rw [hu₂, residue₂_apply, h, map_zero, zero_mul]
    rw [this] at hu₂c
    exact ((map_eq_zero_iff _ (algebraMap k ↥(modularFunctionFieldC k 1)).injective).mp hu₂c.symm)
  have hordu₁ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.ord u₁ = 0 := by
    intro v; rw [hu₁c]; exact (v.hasValue_algebraMap c').ord_eq_zero hc'0
  have hordu₂ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.ord u₂ = 0 := by
    intro v; rw [hu₂c]; exact (v.hasValue_algebraMap c').ord_eq_zero hc'0

  have hQ₁inj : Function.Injective Q₁ := fun i j h => hinj₁ (by simp [h])
  have hQ₂inj : Function.Injective Q₂ := fun i j h => hinj₂ (by simp [h])
  have hE₁T : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictFst =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hi
    split_ifs at hi with h
    · rw [← h]; exact hQ₁ i
    · exact absurd rfl hi
  have hE₂T : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictFst = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact P.not_isStrictFst_of_isStrictSnd (hQ₂ j) hV
  have hE₁T' : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictSnd = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact P.not_isStrictFst_of_isStrictSnd hV (hQ₁ i)
  have hE₂T' : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictSnd =
      ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hj
    split_ifs at hj with h
    · rw [← h]; exact hQ₂ j
    · exact absurd rfl hj
  have hbase₁ : Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  have hbase₂ : Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  have hDfst : (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictFst
      = P.fstDiv D := rfl
  have hDsnd : (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).filter P.IsStrictSnd
      = P.sndDiv D := rfl
  refine ⟨?_, ?_⟩
  ·
    ext v
    by_cases hv : φ (φ v) = v
    · have lhs : Finsupp.mapDomain P.reduceFst (P.fstDiv E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [fstDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₁ i).2 hv
      rw [lhs, rhs]
    · have hlaw := hR.1 (c • f) hG₁ hG₂ hres₁ hres₂ _ hdivG v hv
      have hfilt : (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
          - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).filter P.IsStrictFst =
          P.fstDiv E - ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) - P.fstDiv D := by
        rw [sub_eq_add_neg, sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_neg,
          Finsupp.filter_neg, Finsupp.filter_add, hE₁T, hE₂T, add_zero, ← hDfst, ← sub_eq_add_neg,
          ← sub_eq_add_neg]
        rfl
      rw [hfilt, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
        hdiv₁' v, hbase₁] at hlaw
      have h0 : v.ord (R.residue₁ ⟨c • f, hG₁⟩) + v.ord hb₁ = 0 := by
        rw [← v.ord_mul _ hb₁0]
        · exact hordu₁ v
        · intro h; exact hres₁ (hinjι (by rw [← residue₁_apply, h, map_zero]))
      omega
  ·
    ext v
    by_cases hv : φ (φ v) = v
    · have lhs : Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [sndDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₂ j).2 hv
      rw [lhs, rhs]
    · have hlaw := hR.2.1 (c • f) hG₁ hG₂ hres₁ hres₂ _ hdivG v hv
      have hfilt : (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
          - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).filter P.IsStrictSnd =
          P.sndDiv E - ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) - P.sndDiv D := by
        rw [sub_eq_add_neg, sub_eq_add_neg, Finsupp.filter_add, Finsupp.filter_add, Finsupp.filter_neg,
          Finsupp.filter_neg, Finsupp.filter_add, hE₁T', hE₂T', zero_add, ← hDsnd, ← sub_eq_add_neg,
          ← sub_eq_add_neg]
        rfl
      rw [hfilt, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
        hdiv₂' v, hbase₂] at hlaw
      have h0 : v.ord (R.residue₂ ⟨c • f, hG₂⟩) + v.ord hb₂ = 0 := by
        rw [← v.ord_mul _ hb₂0]
        · exact hordu₂ v
        · intro h; exact hres₂ (hinjι (by rw [← residue₂_apply, h, map_zero]))
      omega

end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.IsModel modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence smulNodePair nodePairsOfPlaces smulNodePair_mem_nodePairsOfPlaces ssPlaces IsAffineGeomPlace arithFrobC deg_eq_one_modularFunctionFieldBar exists_eq_algebraMap_of_hasValue_smul_of_generalPosition exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.IsModel reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue₁ residue₂ residue₁_apply residue₂_apply OrderLawFixed IsModel NodeValueLaw RegularityLaw R₁ mk ι R₂ sectionPair_bounds_of_regularityLaw_of_isModel_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne.ModularCurve"

set_option maxHeartbeats 12800000 in
theorem IsModel.exists_isStrictFst_isStrictSnd_reduce_eq_pic0Mk_eq_of_isGoodDiv'
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (hqN : ¬ q ∣ 1)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hDgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by
  classical

  have hE₀deg : Divisor.degree (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))
      (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) = ((d₁ + d₂ : ℕ) : ℤ) := by
    rw [map_add, map_sum, map_sum]
    simp only [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar, Nat.cast_one,
      mul_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

  obtain ⟨E, hE0, hEdeg, hEdz, hEx⟩ :=
    ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree (1 * q)
      (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      (by rw [hE₀deg]; exact_mod_cast hdeg.ge) (Pic0.mk D)

  have hprin : (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ∈
      Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
    have h := hEx
    rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have h' : -(E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)))
        + (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
        Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := h
    have := neg_mem h'
    convert this using 1
    abel
  obtain ⟨f, hf0, hdivf⟩ := hprin

  obtain ⟨hpush₁, hpush₂⟩ := mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq hqN hR hW hRL Q₁ Q₂ hQ₁ hQ₂
    hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ E hE0 D hDgood hadm hmk f hf0 hdivf

  have hEdeg' : Divisor.degree (K := AlgebraicClosure ℚ) E = ((d₁ + d₂ : ℕ) : ℤ) := hEdeg.trans hE₀deg
  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hEQ⟩ :=
    P.exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv E hE0 Q₁ Q₂ hinj₁ hinj₂ hpush₁ hpush₂ hEdeg'
  refine ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, ?_⟩
  have hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
      - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))) := by
    rw [← hEQ]; exact hEdz
  refine ⟨hdeg0, ?_⟩
  have heq : (⟨_, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      = ⟨E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)), hEdz⟩ := by
    apply Subtype.ext
    simp [hEQ]
  rw [heq]
  exact hEx

end ModularCurve.PlaceSpecialization.ProlongationTuple

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduce_eq_pic0Mk_eq_of_isGoodDiv'
    (fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h))
    hR hW hRL Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ hdeg D hgood hadm hmk

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne (solution)
