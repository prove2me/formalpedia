-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a0a9e091-77da-5c36-b4cd-c4329f2b1b24

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNCore

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

section GeometryN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

private theorem trichotomy (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.IsStrictFst W ∨ P.IsStrictSnd W ∨
    (φ (φ (P.reduceFst W)) = P.reduceFst W ∧ P.reduceSnd W = φ (P.reduceFst W)) := by
  rcases P.d1 W with h | h
  ·
    change P.reduceFst W = φ (P.reduceSnd W) at h
    by_cases hfix : φ (φ (P.reduceSnd W)) = P.reduceSnd W
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [h, hfix]
      · rw [h, hfix]
    · exact Or.inr (Or.inl ⟨h, hfix⟩)
  · change φ (P.reduceFst W) = P.reduceSnd W at h
    by_cases hfix : φ (φ (P.reduceFst W)) = P.reduceFst W
    · exact Or.inr (Or.inr ⟨hfix, h.symm⟩)
    · exact Or.inl ⟨h, hfix⟩

variable {P}

private theorem not_fixed_reduceFst_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := h.2

private theorem not_fixed_reduceSnd_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceSnd W)) ≠ P.reduceSnd W := h.2

private theorem not_fixed_reduceSnd_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst W) : φ (φ (P.reduceSnd W)) ≠ P.reduceSnd W := by
  intro hfix
  apply h.2
  have e : P.reduceSnd W = φ (P.reduceFst W) := h.1.symm
  rw [e] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

private theorem not_fixed_reduceFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := by
  intro hfix
  apply h.2
  have e : P.reduceFst W = φ (P.reduceSnd W) := h.1
  rw [e] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

private theorem not_isStrictSnd_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h1 : P.IsStrictFst W) (h2 : P.IsStrictSnd W) : False := by
  apply h2.2
  have e1 : φ (P.reduceFst W) = P.reduceSnd W := h1.1
  have e2 : P.reduceFst W = φ (P.reduceSnd W) := h2.1
  rw [e2] at e1
  exact e1

end GeometryN

section SeamN

private theorem residue_inv_eq_zero_of_not_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {c : AlgebraicClosure ℚ} (hc : c ∉ A) (hc' : c⁻¹ ∈ A) :
    IsLocalRing.residue A ⟨c⁻¹, hc'⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  apply hc
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ A.zero_mem)
  have h1 : c⁻¹ * (w : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have : (w : AlgebraicClosure ℚ) = c := by
    calc (w : AlgebraicClosure ℚ) = c * (c⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c := by rw [h1, mul_one]
  rw [← this]
  exact w.2

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P)

include R in

private theorem red_inv_eq_zero_of_not_mem {c : AlgebraicClosure ℚ} (hc : c ∉ A) (hc' : c⁻¹ ∈ A) :
    red ⟨c⁻¹, hc'⟩ = 0 := by
  rw [← R.redBar_residue, residue_inv_eq_zero_of_not_mem hc hc', map_zero]

private theorem coeffMap_algebraMap_of_ringHom {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap k ↥(modularFunctionFieldC k N) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  have h1 : ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) c :
      ↥(modularFunctionFieldFullC (ResidueField A) N)) : LaurentSeries (ResidueField A))
        = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c :=
    (IsScalarTower.algebraMap_apply (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)
      (LaurentSeries (ResidueField A)) c).symm
  have h2 : ((algebraMap k ↥(modularFunctionFieldC k N) (R.redBar c) : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = algebraMap k (LaurentSeries k) (R.redBar c) :=
    (IsScalarTower.algebraMap_apply k ↥(modularFunctionFieldC k N) (LaurentSeries k) (R.redBar c)).symm
  rw [h1, h2]
  exact coeffMap_algebraMap_of_ringHom R.redBar c

private theorem algebraMap_mem_integers₁ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff a).mpr a.2

private theorem algebraMap_mem_integers₂ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff a).mpr a.2

private theorem residue₁_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ =
      algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [ProlongationTuple.residue₁_apply, ← R.redBar_residue, ← ι_algebraMap R]
  congr 1
  exact R.R₁.residue_algebraMap a

private theorem residue₂_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ =
      algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [ProlongationTuple.residue₂_apply, ← R.redBar_residue, ← ι_algebraMap R]
  congr 1
  exact R.R₂.residue_algebraMap a

private theorem residue₁_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = R.residue₁ ⟨f, h⟩ -
      algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [← residue₁_algebraMap R a (algebraMap_mem_integers₁ R a), ← map_sub]
  rfl

private theorem residue₂_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = R.residue₂ ⟨f, h⟩ -
      algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [← residue₂_algebraMap R a (algebraMap_mem_integers₂ R a), ← map_sub]
  rfl

private theorem residue₁_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (ha : red a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₁.integers) = 1 - ⟨_, algebraMap_mem_integers₁ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₁_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

private theorem residue₂_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (ha : red a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₂.integers) = 1 - ⟨_, algebraMap_mem_integers₂ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₂_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

private theorem residue_ne_zero_iff₁ (x : R.R₁.integers) : R.residue₁ x ≠ 0 ↔ R.R₁.residue x ≠ 0 := by
  rw [ProlongationTuple.residue₁_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

private theorem residue_ne_zero_iff₂ (x : R.R₂.integers) : R.residue₂ x ≠ 0 ↔ R.R₂.residue x ≠ 0 := by
  rw [ProlongationTuple.residue₂_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

end SeamN

section FrobAffine

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
  (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

omit [CharP k q] in

private theorem exists_pow_eq_of_isAlgClosed (c : k) : ∃ d : k, d ^ q = c :=
  IsAlgClosed.exists_pow_nat_eq c (Fact.out : q.Prime).pos

private theorem isAffineGeomPlace_of_frob
    (hfin : {v : Place k ↥(modularFunctionFieldC k N) | ¬ IsAffineGeomPlace k N v}.Finite)
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (v : Place k ↥(modularFunctionFieldC k N)) (h : IsAffineGeomPlace k N (φ v)) : IsAffineGeomPlace k N v := by
  classical
  by_contra hv
  have hinj := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  have hsurj := ModularCurve.frobOnPlacesGeomLevel_surjective k N data hKr (exists_pow_eq_of_isAlgClosed (q := q))
  set S := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ ¬ IsAffineGeomPlace k N w := fun w => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hsub : S ⊆ S.image φ := by
    intro w hw
    obtain ⟨u, rfl⟩ := hsurj w
    refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
    rw [hmemS] at hw ⊢
    exact fun hu => hw (hfwd u hu)
  have hcard : (S.image φ).card ≤ S.card := Finset.card_image_le
  have heq : S.image φ = S := (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hvS : v ∈ S := (hmemS v).mpr hv
  have : φ v ∈ S := by rw [← heq]; exact Finset.mem_image_of_mem _ hvS
  exact ((hmemS _).mp this) h

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {red : A →+* k}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

omit [IsAlgClosed k] in
private theorem not_isAffineGeomPlace_reduceSnd_of_reduceFst
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (h : ¬ IsAffineGeomPlace k N (P.reduceFst V)) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) := by
  intro hs
  rcases P.d1 V with e | e
  · change P.reduceFst V = φ (P.reduceSnd V) at e
    exact h (e ▸ hfwd _ hs)
  · change φ (P.reduceFst V) = P.reduceSnd V at e
    exact h (hbwd _ (e ▸ hs))

omit [IsAlgClosed k] in
private theorem not_isAffineGeomPlace_reduceFst_of_reduceSnd
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (h : ¬ IsAffineGeomPlace k N (P.reduceSnd V)) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) := by
  intro hs
  rcases P.d1 V with e | e
  · change P.reduceFst V = φ (P.reduceSnd V) at e
    exact h (hbwd _ (e ▸ hs))
  · change φ (P.reduceFst V) = P.reduceSnd V at e
    exact h (e ▸ hfwd _ hs)

omit [IsAlgClosed k] in

private theorem not_isAffineGeomPlace_reduceSnd_of_isInftySide
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : ProlongationTuple.IsInftySide P V) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
  not_isAffineGeomPlace_reduceSnd_of_reduceFst data hKr P hfwd hbwd (hInftyNA V hV)

omit [IsAlgClosed k] in

private theorem not_isAffineGeomPlace_reduceFst_of_isZeroSide
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : ProlongationTuple.IsZeroSide P V) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) :=
  not_isAffineGeomPlace_reduceFst_of_reduceSnd data hKr P hfwd hbwd (hZeroNA V hV)

end FrobAffine

end MOVNCore

section Dict

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem not_isAffineGeomPlace_reduceSnd_of_isCuspidal'
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ProlongationTuple.IsCuspidal' P V) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ with hjN
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q jN = ProlongationTuple.jQFun N q := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [coeffEmb, coeffMap_qExpand]
  have he : 0 < Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) V := by
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
    exact V.ramificationIndex_pos (F := modularFunctionFieldBar N)
  have hcusp : ∀ a : A, (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hle := hV a
    have key := Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, hβj, AlgHom.commutes] at key
    rw [key] at hle
    by_contra hpos
    push Not at hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he) hpos))
  have hpole := P.d0_j_pole (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) hcusp
  intro haff
  have h0 := (P.reduceSnd V).ord_nonneg_of_mem haff.1
  exact absurd hpole (not_lt.mpr h0)

end MOVNAsm

end Dict

section Zone

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}

omit [DecidableEq k] in
open Classical in

private theorem finite_setOf_not_isAffineGeomPlace :
    {v : Place k ↥(modularFunctionFieldC k N) | ¬ IsAffineGeomPlace k N v}.Finite := by
  classical
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hj0 : (jGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jGeomGen_sub_algebraMap_ne_zero k N 0
  have hjN0 : (jNGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jNGeomGen_sub_algebraMap_ne_zero k N 0
  haveI hPD : HasPrincipalDivisors k (modularFunctionFieldC k N) := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen k N) hj0
  obtain ⟨DN, hDN, -⟩ := hPD.exists_divisor (jNGeomGen k N) hjN0
  refine (Dj.support.finite_toSet.union DN.support.finite_toSet).subset ?_
  intro v hv
  rw [Set.mem_setOf_eq, IsAffineGeomPlace, not_and_or] at hv
  rcases hv with h | h
  · left
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDj]
    intro h0
    exact h (v.mem_of_ord_nonneg hj0 (le_of_eq h0.symm))
  · right
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDN]
    intro h0
    exact h (v.mem_of_ord_nonneg hjN0 (le_of_eq h0.symm))

private theorem mem_ssPlaces_frob_iff
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (v : Place k ↥(modularFunctionFieldC k N)) :
    frobOnPlacesGeomLevel k N data hKr v ∈ ssPlaces q N k ↔ v ∈ ssPlaces q N k := by
  classical
  have hfwd : ∀ w ∈ ssPlaces q N k, frobOnPlacesGeomLevel k N data hKr w ∈ ssPlaces q N k := by
    intro w hw
    rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
    exact ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hw
  refine ⟨fun h => ?_, hfwd v⟩
  have hinj := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  have hmaps : Set.MapsTo (frobOnPlacesGeomLevel k N data hKr) (↑W : Set _) (↑W : Set _) := by
    intro w hw
    exact Finset.mem_coe.mpr ((hW _).mpr (hfwd w ((hW w).mp (Finset.mem_coe.mp hw))))
  have hsurj : Set.SurjOn (frobOnPlacesGeomLevel k N data hKr) (↑W : Set _) (↑W : Set _) :=
    (Finset.surjOn_of_injOn_of_card_le _ (fun w hw => hmaps hw) (hinj.injOn) le_rfl)
  obtain ⟨w, hw, hwv⟩ := hsurj (Finset.mem_coe.mpr ((hW _).mpr h))
  rw [hinj hwv] at hw
  exact (hW v).mp (Finset.mem_coe.mp hw)

private theorem exists_zone
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (T : Finset (Place k ↥(modularFunctionFieldC k N))) (hT : ∀ t ∈ T, t ∉ ssPlaces q N k) :
    ∃ Z : Finset (Place k ↥(modularFunctionFieldC k N)),
      (∀ v ∈ T, v ∈ Z) ∧
      (∀ v ∈ T, frobOnPlacesGeomLevel k N data hKr v ∈ Z) ∧
      (∀ v, frobOnPlacesGeomLevel k N data hKr v ∈ T → v ∈ Z) ∧
      (∀ v, ¬ IsAffineGeomPlace k N v → v ∈ Z) ∧
      (∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        v ∉ ssPlaces q N k → v ∈ Z) ∧
      (∀ v ∈ Z, v ∉ ssPlaces q N k) := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hinj : Function.Injective φ := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  obtain ⟨NA, hNA⟩ := (finite_setOf_not_isAffineGeomPlace (k := k) (N := N)).exists_finset_coe
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  obtain ⟨FX, hFX⟩ := ((ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self k N data hKr).diff
    (t := ssPlaces q N k)).exists_finset_coe
  refine ⟨T ∪ T.image φ ∪ T.preimage φ hinj.injOn ∪ NA ∪ FX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp [hv]
  · intro v hv; simp only [Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  · intro v hv; simp only [Finset.mem_union, Finset.mem_preimage]; exact Or.inl (Or.inl (Or.inr hv))
  · intro v hv
    simp only [Finset.mem_union]
    left; right
    rw [← Finset.mem_coe, hNA]; exact hv
  · intro v hfix hss
    simp only [Finset.mem_union]
    right
    rw [← Finset.mem_coe, hFX]
    exact ⟨hfix, hss⟩
  · intro v hv hss
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_preimage] at hv
    rcases hv with (((hv | ⟨w, hw, rfl⟩) | hv) | hv) | hv
    · exact hT v hv hss
    · exact hT w hw ((mem_ssPlaces_frob_iff W hW w).mp hss)
    · exact hT _ hv ((mem_ssPlaces_frob_iff W hW v).mpr hss)
    · rw [← Finset.mem_coe, hNA, Set.mem_setOf_eq] at hv
      exact hv hss.2.1
    · rw [← Finset.mem_coe, hFX] at hv
      exact hv.2 hss

end MOVNAsm

end Zone

section Good

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem isStrict_of_mem_support
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (Z : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hZfix : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v ∉ ssPlaces q N k → v ∈ Z)
    (htri : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨
        (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) = P.reduceFst V ∧
          P.reduceSnd V = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hDpole : ∀ V, D V < 0 → P.IsStrictFst V ∨ P.IsStrictSnd V)
    (htube : ∀ V, P.reduceFst V ∈ ssPlaces q N k → 0 < D V → False)
    (hcount : ∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False) :
    ∀ V ∈ D.support, V ≠ V₀ → P.IsStrictFst V ∨ P.IsStrictSnd V := by
  intro V hV hne
  have hD0 : D V ≠ 0 := Finsupp.mem_support_iff.mp hV
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · exact hDpole V hneg
  · rcases htri V with h | h | ⟨hfix, hsnd⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      by_cases hss : P.reduceFst V ∈ ssPlaces q N k
      · exact htube V hss hpos
      · have h1 : P.reduceFst V ∈ Z := hZfix _ hfix hss
        have hfix' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V))
            = P.reduceSnd V := by rw [hsnd, hfix]
        have hss' : P.reduceSnd V ∉ ssPlaces q N k := by
          rw [hsnd, mem_ssPlaces_frob_iff W hW]; exact hss
        have h2 : P.reduceSnd V ∈ Z := hZfix _ hfix' hss'
        exact hcount V hne (by omega) h1 h2

end MOVNAsm

end Good

section Count2

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

section Deg
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem degree_eq_sum_of_deg_eq_one (h1 : ∀ w : Place K F, w.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ w ∈ D.support, D w := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  show D w * (w.deg : ℤ) = D w
  rw [h1, Nat.cast_one, mul_one]

private theorem degree_mapDomain_of_deg_eq_one' {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (r : Place K F → Place K' F')
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

open Classical in
private theorem degree_filter_add_filter_not (D : Divisor K F) (p : Place K F → Prop) [DecidablePred p] :
    Divisor.degree (D.filter p) + Divisor.degree (D.filter fun w => ¬ p w) = Divisor.degree D := by
  rw [← map_add, Finsupp.filter_add_filter_not]

private theorem forall_of_degree_filter_le (h1 : ∀ w : Place K F, w.deg = 1) (D : Divisor K F) (p : Place K F → Prop)
    [DecidablePred p] (V₀ : Place K F)
    (hnonneg : ∀ V, ¬ p V → 0 ≤ D V)
    (hbudget : Divisor.degree (D.filter fun w => ¬ p w) ≤ (D.filter fun w => ¬ p w) V₀) :
    ∀ V ∈ D.support, V ≠ V₀ → p V := by
  classical
  intro V hV hne
  by_contra hp
  have hDV : 0 < D V := lt_of_le_of_ne (hnonneg V hp) (Ne.symm (Finsupp.mem_support_iff.mp hV))
  set E := D.filter fun w => ¬ p w with hE
  have hE0 : ∀ W, 0 ≤ E W := fun W => by
    rw [hE, Finsupp.filter_apply]
    by_cases h : p W
    · rw [if_neg (not_not_intro h)]
    · rw [if_pos h]; exact hnonneg W h
  have hEV : E V = D V := by rw [hE, Finsupp.filter_apply, if_pos hp]
  have hmem : V ∈ E.support := by rw [Finsupp.mem_support_iff, hEV]; exact hDV.ne'
  rw [degree_eq_sum_of_deg_eq_one h1] at hbudget
  have key : E V₀ + E V ≤ ∑ w ∈ E.support, E w := by
    by_cases h0 : V₀ ∈ E.support
    · rw [← Finset.add_sum_erase _ _ h0]
      refine add_le_add le_rfl ?_
      have hmem' : V ∈ E.support.erase V₀ := Finset.mem_erase.mpr ⟨hne, hmem⟩
      rw [← Finset.add_sum_erase _ _ hmem']
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => hE0 w)
    · rw [Finsupp.notMem_support_iff.mp h0, zero_add, ← Finset.add_sum_erase _ _ hmem]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => hE0 w)
  have : E V ≤ 0 := by linarith
  rw [hEV] at this
  exact absurd hDV (not_lt.mpr this)

end Deg

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in

private theorem degree_filter_isStrictFst_eq
    (R : ProlongationTuple P) (hDF : R.DivisorLawFst)
    (h1up : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.deg = 1)
    (h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1)
    (hstrict_nf : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hf₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (D₁ : Divisor k ↥(modularFunctionFieldC k N)) (hD₁ : ∀ v, D₁ v = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₁ : Divisor.degree D₁ = 0) :
    Divisor.degree (D.filter P.IsStrictFst)
      = - Divisor.degree (D₁.filter fun v =>
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hpush : Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) = D₁.filter fun v => ¬ (φ (φ v) = v) := by
    ext v
    rw [Finsupp.filter_apply]
    by_cases hv : φ (φ v) = v
    · rw [if_neg (not_not_intro hv)]
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [Finsupp.single_apply, if_neg]
      intro hWv
      have hWs : P.IsStrictFst W := by
        rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
        by_contra hns; rw [if_neg hns] at hW; exact hW rfl
      exact hstrict_nf W hWs (by rw [hWv]; exact hv)
    · rw [if_pos hv, hDF f h₁ h₂ hf₁ hf₂ D hD v hv, hD₁]
  have hdeg := degree_mapDomain_of_deg_eq_one' P.reduceFst h1up h1dn (D.filter P.IsStrictFst)
  rw [hpush] at hdeg
  have hsplit := degree_filter_add_filter_not D₁ (fun v => φ (φ v) = v)
  rw [hdegD₁] at hsplit
  linarith

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in

private theorem degree_filter_isStrictSnd_eq
    (R : ProlongationTuple P) (hDS : R.DivisorLawSnd)
    (h1up : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.deg = 1)
    (h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1)
    (hstrict_nf : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hf₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (D₂ : Divisor k ↥(modularFunctionFieldC k N)) (hD₂ : ∀ v, D₂ v = v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₂ : Divisor.degree D₂ = 0) :
    Divisor.degree (D.filter P.IsStrictSnd)
      = - Divisor.degree (D₂.filter fun v =>
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hpush : Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) = D₂.filter fun v => ¬ (φ (φ v) = v) := by
    ext v
    rw [Finsupp.filter_apply]
    by_cases hv : φ (φ v) = v
    · rw [if_neg (not_not_intro hv)]
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [Finsupp.single_apply, if_neg]
      intro hWv
      have hWs : P.IsStrictSnd W := by
        rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
        by_contra hns; rw [if_neg hns] at hW; exact hW rfl
      exact hstrict_nf W hWs (by rw [hWv]; exact hv)
    · rw [if_pos hv, hDS f h₁ h₂ hf₁ hf₂ D hD v hv, hD₂]
  have hdeg := degree_mapDomain_of_deg_eq_one' P.reduceSnd h1up h1dn (D.filter P.IsStrictSnd)
  rw [hpush] at hdeg
  have hsplit := degree_filter_add_filter_not D₂ (fun v => φ (φ v) = v)
  rw [hdegD₂] at hsplit
  linarith

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in

private theorem degree_filter_not_strict_eq
    (R : ProlongationTuple P) (hDF : R.DivisorLawFst) (hDS : R.DivisorLawSnd)
    (h1up : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.deg = 1)
    (h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1)
    (hstrict_nf₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V)
    (hstrict_nf₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V)
    (hnot_both : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V → ¬ P.IsStrictSnd V)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hf₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (hdegD : Divisor.degree D = 0)
    (D₁ : Divisor k ↥(modularFunctionFieldC k N)) (hD₁ : ∀ v, D₁ v = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₁ : Divisor.degree D₁ = 0)
    (D₂ : Divisor k ↥(modularFunctionFieldC k N)) (hD₂ : ∀ v, D₂ v = v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₂ : Divisor.degree D₂ = 0) :
    Divisor.degree (D.filter fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))
      = Divisor.degree (D₁.filter fun v =>
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
        + Divisor.degree (D₂.filter fun v =>
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) := by
  classical
  have e1 := degree_filter_isStrictFst_eq R hDF h1up h1dn hstrict_nf₁ f h₁ h₂ hf₁ hf₂ D hD D₁ hD₁ hdegD₁
  have e2 := degree_filter_isStrictSnd_eq R hDS h1up h1dn hstrict_nf₂ f h₁ h₂ hf₁ hf₂ D hD D₂ hD₂ hdegD₂
  have hpart : D.filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)
      = D.filter P.IsStrictFst + D.filter P.IsStrictSnd := by
    ext V
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    by_cases ha : P.IsStrictFst V
    · rw [if_pos (Or.inl ha), if_pos ha, if_neg (hnot_both V ha), add_zero]
    · by_cases hb : P.IsStrictSnd V
      · rw [if_pos (Or.inr hb), if_neg ha, if_pos hb, zero_add]
      · rw [if_neg (by tauto), if_neg ha, if_neg hb, add_zero]
  have hsplit := degree_filter_add_filter_not D (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)
  rw [hpart, map_add, hdegD] at hsplit
  linarith

end MOVNAsm

end Count2

section Glue

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in

private theorem degree_filter_fixed_le
    (h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1)
    (E : Divisor k ↥(modularFunctionFieldC k N)) (d : Place k ↥(modularFunctionFieldC k N))
    (hE : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v → v ≠ d → E v = 0) :
    Divisor.degree (E.filter fun v =>
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
      = if frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr d) = d then E d else 0 := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hsingle : (E.filter fun v => φ (φ v) = v) = Finsupp.single d (if φ (φ d) = d then E d else 0) := by
    ext v
    rw [Finsupp.filter_apply, Finsupp.single_apply]
    by_cases hvd : d = v
    · subst hvd; by_cases h : φ (φ d) = d <;> simp [h]
    · rw [if_neg hvd]
      by_cases h : φ (φ v) = v
      · rw [if_pos h]; exact hE v h (Ne.symm hvd)
      · rw [if_neg h]
  rw [hsingle, Divisor.degree_single, h1dn, Nat.cast_one, mul_one]

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in

private theorem isStrict_of_tables
    (R : ProlongationTuple P) (hDF : R.DivisorLawFst) (hDS : R.DivisorLawSnd)
    (h1up : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W.deg = 1)
    (h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1)
    (htri : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨
        (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) = P.reduceFst V ∧
          P.reduceSnd V = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)))
    (hstrict_nf₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V)
    (hstrict_nf₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V)
    (hstrict_nf₁' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V)
    (hstrict_nf₂' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V)
    (hnot_both : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V → ¬ P.IsStrictSnd V)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hf₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (hdegD : Divisor.degree D = 0)
    (D₁ : Divisor k ↥(modularFunctionFieldC k N)) (hD₁ : ∀ v, D₁ v = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₁ : Divisor.degree D₁ = 0)
    (D₂ : Divisor k ↥(modularFunctionFieldC k N)) (hD₂ : ∀ v, D₂ v = v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)))
    (hdegD₂ : Divisor.degree D₂ = 0)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDV₀ : 1 ≤ D V₀)
    (htab₁ : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v ≠ P.reduceFst V₀ → D₁ v = 0)
    (htab₂ : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v ≠ P.reduceSnd V₀ → D₂ v = 0)
    (hd₁ : 0 ≤ D₁ (P.reduceFst V₀)) (hd₁' : D₁ (P.reduceFst V₀) ≤ 1)
    (hd₂ : 0 ≤ D₂ (P.reduceSnd V₀)) (hd₂' : D₂ (P.reduceSnd V₀) ≤ 1)
    (hnb : ¬ (D₁ (P.reduceFst V₀) = 1 ∧ D₂ (P.reduceSnd V₀) = 1))
    (hpole : ∀ V, D V < 0 → P.IsStrictFst V ∨ P.IsStrictSnd V) :
    ∀ V ∈ D.support, V ≠ V₀ → P.IsStrictFst V ∨ P.IsStrictSnd V := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hns := degree_filter_not_strict_eq R hDF hDS h1up h1dn hstrict_nf₁ hstrict_nf₂ hnot_both f h₁ h₂ hf₁ hf₂ D hD
    hdegD D₁ hD₁ hdegD₁ D₂ hD₂ hdegD₂
  rw [degree_filter_fixed_le h1dn D₁ (P.reduceFst V₀) htab₁,
    degree_filter_fixed_le h1dn D₂ (P.reduceSnd V₀) htab₂] at hns
  refine forall_of_degree_filter_le h1up D (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V) V₀ ?_ ?_
  · intro V hV
    by_contra hlt
    push Not at hlt
    exact hV (hpole V hlt)
  · rw [hns, Finsupp.filter_apply]
    rcases htri V₀ with h0 | h0 | ⟨hfix, hsnd⟩
    ·
      rw [if_neg (hstrict_nf₁ V₀ h0), if_neg (hstrict_nf₁' V₀ h0), if_neg (not_not_intro (Or.inl h0))]
      simp
    · rw [if_neg (hstrict_nf₂' V₀ h0), if_neg (hstrict_nf₂ V₀ h0), if_neg (not_not_intro (Or.inr h0))]
      simp
    · have hfix₂ : φ (φ (P.reduceSnd V₀)) = P.reduceSnd V₀ := by rw [hsnd, hfix]
      have hnot : ¬ (P.IsStrictFst V₀ ∨ P.IsStrictSnd V₀) := by
        rintro (h | h)
        · exact hstrict_nf₁ V₀ h hfix
        · exact hstrict_nf₂ V₀ h hfix₂
      rw [if_pos hfix, if_pos hfix₂, if_pos hnot]
      omega

end MOVNAsm

end Glue

private theorem MOVNAsm.finsuppDegree_sum_single {α ι : Type*} [DecidableEq α] [Fintype ι] (Q : ι → α) :
    Finsupp.degree (∑ i, Finsupp.single (Q i) (1 : ℤ)) = Fintype.card ι := by
  classical
  rw [map_sum]
  simp [Finsupp.degree_single]

private theorem MOVNAsm.finsuppDegree_eq_sum {α : Type*} (D : α →₀ ℤ) :
    Finsupp.degree D = ∑ i ∈ D.support, D i := rfl

private theorem MOVNAsm.finsuppDegree_mapDomain {α β : Type*} (r : α → β) (D : α →₀ ℤ) :
    Finsupp.degree (Finsupp.mapDomain r D) = Finsupp.degree D := by
  classical
  rw [MOVNAsm.finsuppDegree_eq_sum, MOVNAsm.finsuppDegree_eq_sum]
  show (Finsupp.mapDomain r D).sum (fun _ n => n) = D.sum (fun _ n => n)
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem MOVNAsm.divisorDegree_eq_finsuppDegree {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h1 : ∀ w : Place K F, w.deg = 1) (D : Divisor K F) :
    Divisor.degree D = Finsupp.degree D := by
  rw [MOVNAsm.finsuppDegree_eq_sum]
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  show D w * (w.deg : ℤ) = D w
  rw [h1, Nat.cast_one, mul_one]

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed) :
        ∀ (T : Finset (Place k ↥(modularFunctionFieldC k N)))
          (hT : ∀ t ∈ T, t ∉ ssPlaces q N k)
          (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T),
          ∃ (f : ↥(modularFunctionFieldBar (N * q)))
            (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
            f ≠ 0 ∧
            (∃ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
              R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0) ∧
            (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
            (∀ V ∈ D.support, V ≠ V₀ → P.IsStrictFst V ∨ P.IsStrictSnd V) ∧
            (∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ,
              arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀ →
                arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f = f := by
  intro T hT V₀ hV₀
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  haveI hIC : IsCurveOver k ↥(modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V :=
    fun V h => ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P V h
  have hsplit : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V :=
    fun V h => ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN V h
  have hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V) :=
    fun V h => ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P V h.1
  have hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
    fun V h => MOVNAsm.not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P V h.1
  have hφaff : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v →
      IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) :=
    fun v h => ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v h
  have hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N),
      IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) → IsAffineGeomPlace k N v :=
    fun v h => MOVNCore.isAffineGeomPlace_of_frob data hKr
      (MOVNAsm.finite_setOf_not_isAffineGeomPlace (k := k) (N := N)) hφaff v h
  have hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
    fun V h => MOVNCore.not_isAffineGeomPlace_reduceSnd_of_isInftySide data hKr P hφaff hbwd hInftyNA V h
  have hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V) :=
    fun V h => MOVNCore.not_isAffineGeomPlace_reduceFst_of_isZeroSide data hKr P hφaff hbwd hZeroNA V h
  have hNss : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, s.1 ∈ ssPlaces q N k ∧ s.2 ∈ ssPlaces q N k := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff _ _ _).mp hs
    exact ⟨(hW w).mp hw, ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w ((hW w).mp hw)⟩
  have hzone := fun (T' : Finset (Place k ↥(modularFunctionFieldC k N))) (hT' : ∀ t ∈ T', t ∉ ssPlaces q N k) =>
    MOVNAsm.exists_zone (data := data) (hKr := hKr) W hW T' hT'
  have hAUX := fun (B : Finset (Place k ↥(modularFunctionFieldC k N))) (m₁ m₂ : ℕ) =>
    ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq P hqN B m₁ m₂
  have hEq : modularFunctionFieldFullC k N = modularFunctionFieldC k N :=
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN).symm
  have hINTERP := ModularCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC k N
  rw [hEq] at hINTERP
  have hREALN := fun (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
      D hD hgood hDfix hdeg₁ hdeg₂ g₁ g₂ hg₁ hg₂ hnode =>
    ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv hqN hW R hR hRL hval hO S hS D hD hgood hDfix hdeg₁ hdeg₂ g₁ g₂ hg₁ hg₂ hnode
  have hιbij := ModularCurve.PlaceSpecialization.ProlongationTuple.iota_bijective_of_level R hqN
  let toFull : ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    Function.surjInv hιbij.2
  have ι_toFull : ∀ g, R.ι (toFull g) = g := fun g => Function.surjInv_eq hιbij.2 g
  obtain ⟨Z, f, h₁, h₂, D, ⟨hZT, hZna, hZfix, hZss⟩, hf0, hr₁, hr₂, hD, hDV₀, hpole, htab₁, htab₂, hpat, hZcount, hTform, hfinv⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq_of_isModel (P := P) R hR hO W hW hRL hval hqN hcusp hsplit hInftyNA hInftyNA' hZeroNA hZeroNA'
      hφaff hNss hzone hAUX hINTERP hREALN toFull ι_toFull T hT V₀ hV₀
  refine ⟨f, D, hf0, ⟨h₁, h₂, hr₁, hr₂⟩, hD, hDV₀, ?_, hTform, hfinv⟩
  obtain ⟨hDF, hDS, -, -⟩ := hR
  have h1up : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), W'.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)
  have h1dn : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hrf₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := (MOVNCore.residue_ne_zero_iff₁ R _).mp hr₁
  have hrf₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := (MOVNCore.residue_ne_zero_iff₂ R _).mp hr₂
  obtain ⟨D', hD', hdegD'⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  have hDD' : D = D' := Finsupp.ext fun V => by rw [hD, hD']
  have hdegD : Divisor.degree D = 0 := by rw [hDD']; exact hdegD'
  haveI hPD : HasPrincipalDivisors k ↥(modularFunctionFieldC k N) := IsCurveOver.hasPrincipalDivisors
  have hr₁0 : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := hr₁
  have hr₂0 : (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := hr₂
  obtain ⟨D₁, hD₁, hdegD₁⟩ := hPD.exists_divisor _ hr₁0
  obtain ⟨D₂, hD₂, hdegD₂⟩ := hPD.exists_divisor _ hr₂0
  have hfixZW : ∀ v : Place k ↥(modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v → v ∈ Z ∨ v ∈ W := by
    intro v hv
    by_cases hss : v ∈ ssPlaces q N k
    · exact Or.inr ((hW v).mpr hss)
    · exact Or.inl (hZfix v hv hss)
  refine MOVNAsm.isStrict_of_tables R hDF hDS h1up h1dn (MOVNCore.trichotomy P)
    (fun V h => MOVNCore.not_fixed_reduceFst_of_isStrictFst h) (fun V h => MOVNCore.not_fixed_reduceSnd_of_isStrictSnd h)
    (fun V h => MOVNCore.not_fixed_reduceSnd_of_isStrictFst h) (fun V h => MOVNCore.not_fixed_reduceFst_of_isStrictSnd h)
    (fun V h1 h2 => MOVNCore.not_isStrictSnd_of_isStrictFst h1 h2)
    f h₁ h₂ hrf₁ hrf₂ D hD hdegD D₁ hD₁ hdegD₁ D₂ hD₂ hdegD₂ V₀ (by omega)
    (fun v hv hne => by rw [hD₁]; exact htab₁ v (hfixZW v hv) hne)
    (fun v hv hne => by rw [hD₂]; exact htab₂ v (hfixZW v hv) hne)
    (by rw [hD₁]; rcases hpat with ⟨h, -⟩ | ⟨h, -⟩ <;> omega)
    (by rw [hD₁]; rcases hpat with ⟨h, -⟩ | ⟨h, -⟩ <;> omega)
    (by rw [hD₂]; rcases hpat with ⟨-, h⟩ | ⟨-, h⟩ <;> omega)
    (by rw [hD₂]; rcases hpat with ⟨-, h⟩ | ⟨-, h⟩ <;> omega)
    (by rw [hD₁, hD₂]; rcases hpat with ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega)
    (fun V hV => by rcases hpole V hV with ⟨h, -⟩ | ⟨h, -⟩; exacts [Or.inl h, Or.inr h])

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel (solution)
