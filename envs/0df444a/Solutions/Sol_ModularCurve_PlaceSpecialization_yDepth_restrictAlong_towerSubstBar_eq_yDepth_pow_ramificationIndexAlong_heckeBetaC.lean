-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d748d985-8a40-50be-9b5a-812654fb078b

import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_restrictAlong_eq_restrictAlong_sp_of_isModel_of_fixed_of_isAffineGeomPlace
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve

namespace YDepthSubstAux

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

theorem evalAt_eq_of_hasValue (v : Place K F) (hv : v.IsRational) {f : F} {a : K}
    (h : v.HasValue f a) : v.evalAt f = a :=
  (hasValue_evalAt v hv h.mem).unique h

theorem isUnit_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
  (hasValue_evalAt v hv hf).isUnit h

theorem evalAt_ne_zero_of_isUnit (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) :
    v.evalAt f ≠ 0 := by
  intro h0
  have h1 : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h
  rw [← v.algebraMap_evalAt hv hf, h0, map_zero] at h1
  exact h1 rfl

theorem evalAt_pow (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (n : ℕ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih, pow_succ]

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (f : F) : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.mem_restrict_iff

theorem HasValue.of_restrict [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    (w : Place K F') {f : F} {a : K} (h : (w.restrict F).HasValue f a) :
    w.HasValue (algebraMap F F' f) a := by
  obtain ⟨hf, hres⟩ := h
  have hf' : algebraMap F F' f ∈ w.toValuationSubring := w.mem_restrict_iff.mp hf
  refine ⟨hf', ?_⟩
  have key := congrArg (Place.restrictResidueMap F w) hres
  rw [Place.restrictResidueMap_residue] at key
  have h1 : (Place.restrictInclusion F w ⟨f, hf⟩ : w.toValuationSubring) = ⟨algebraMap F F' f, hf'⟩ :=
    Subtype.ext rfl
  rw [h1] at key
  rw [key]
  have h2 := (IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField a)
  rw [Place.algebraMap_residueField_eq] at h2
  exact h2.symm

theorem HasValue.of_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    {f : F} {a : K} (h : (w.restrictAlong φ hφ).HasValue f a) : w.HasValue (φ f) a := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact HasValue.of_restrict w h

theorem evalAt_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.IsRational) (hw' : (w.restrictAlong φ hφ).IsRational) {f : F}
    (hf : f ∈ (w.restrictAlong φ hφ).toValuationSubring) :
    (w.restrictAlong φ hφ).evalAt f = w.evalAt (φ f) :=
  (evalAt_eq_of_hasValue w hw
    (HasValue.of_restrictAlong φ hφ w (hasValue_evalAt _ hw' hf))).symm

theorem exists_isUnit_map_of_evalAt_ne_zero (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.IsRational) (hw' : (w.restrictAlong φ hφ).IsRational) {f : F}
    (hf : f ∈ (w.restrictAlong φ hφ).toValuationSubring) (hne : (w.restrictAlong φ hφ).evalAt f ≠ 0) :
    ∃ hm : φ f ∈ w.toValuationSubring, IsUnit (⟨φ f, hm⟩ : w.toValuationSubring) := by
  have hm : φ f ∈ w.toValuationSubring := (mem_restrictAlong_iff φ hφ w f).mp hf
  rw [evalAt_restrictAlong φ hφ w hw hw' hf] at hne
  exact ⟨hm, isUnit_of_evalAt_ne_zero w hw hm hne⟩

theorem ramificationIndexAlong_eq_one_of_surjective (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hsurj : Function.Surjective φ) (w : Place K F') :
    w.ramificationIndexAlong φ = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨f, hf⟩ := hsurj (π : F')
  have h1 : w.ord (φ f) = 1 := by rw [hf]; exact w.ord_coe_irreducible hπ
  have h2 := w.ord_restrictAlong φ hφ f
  rw [h1] at h2
  have h3 : (0 : ℤ) ≤ (w.ramificationIndexAlong φ : ℤ) := Int.natCast_nonneg _
  have h4 := Int.eq_one_of_mul_eq_one_right h3 h2.symm
  exact_mod_cast h4

theorem ord_eq_ramificationIndexAlong_mul_ord {F'' : Type*} [Field F''] [Algebra K F'']
    (incl : F' →ₐ[K] F'') (hincl : incl.toRingHom.IsIntegral) (hsurj : Function.Surjective incl)
    (β : F →ₐ[K] F'') (hβ : β.toRingHom.IsIntegral)
    (y₁ : Place K F'') {y : Place K F'} {w : Place K F}
    (hy : y₁.restrictAlong incl hincl = y) (hw : y₁.restrictAlong β hβ = w)
    {z : F'} {r : F} (h : incl z = β r) :
    y.ord z = y₁.ramificationIndexAlong β * w.ord r := by
  have h1 := y₁.ord_restrictAlong β hβ r
  rw [hw] at h1
  have h2 := y₁.ord_restrictAlong incl hincl z
  rw [hy, ramificationIndexAlong_eq_one_of_surjective incl hincl hsurj y₁, Nat.cast_one, one_mul, h] at h2
  exact h2.symm.trans h1

theorem HasValue.ne_zero_of_ord_eq_zero (v : Place K F) {g : F} {a : K} (h : v.HasValue g a)
    (hg : g ≠ 0) (hord : v.ord g = 0) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg hord
  have h1 : IsLocalRing.residue v.toValuationSubring ⟨g, hm⟩ ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
  apply h1
  have h2 := h.residue_eq
  rw [map_zero] at h2
  exact h2

end Generic

section NodeRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : PlaceSpecialization.ProlongationTuple P)

local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => (↥(modularFunctionFieldBar (N * q)) : Type)

theorem inv_mem_of_isUnit {L : Type*} [Field L] {S : ValuationSubring L} {f : L} (hf : f ∈ S)
    (hu : IsUnit (⟨f, hf⟩ : S)) : f⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : L) = f := by rw [hu]
  have h1 : f * (((u⁻¹ : Sˣ) : S) : L) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      OneMemClass.coe_one]
  have h2 : (((u⁻¹ : Sˣ) : S) : L) = f⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [← h2]
  exact SetLike.coe_mem _

theorem evalAt_coord_ne_zero [PerfectField k] {K : IntermediateField ℚ Qb}
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)
    {ϖ : ↥(NodeLocalized.coeffSubring A K)} (hϖ0 : (ϖ : Qb) ≠ 0)
    (hxy : ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)),
      1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place Qb FF) (hV : P.reduceFst V = w) (hVr : V.IsRational) :
    V.evalAt (c.x : FF) ≠ 0 ∧ V.evalAt (c.y : FF) ≠ 0 := by
  obtain ⟨E, u, _hE, hu, hxy⟩ := hxy
  have hxO : (c.x : FF) ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers c.x.2.1 hV
  have hyO : (c.y : FF) ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers c.y.2.1 hV
  have huO : (u : FF) ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers u.2.1 hV
  obtain ⟨u', huu'⟩ := hu.exists_right_inv
  have hu'O : (u' : FF) ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers u'.2.1 hV
  have hu1 : V.evalAt (u : FF) * V.evalAt (u' : FF) = 1 := by
    rw [← V.evalAt_mul hVr huO hu'O]
    have : ((u * u' : ↥(R.nodeIntegersOver K w)) : FF) = (u : FF) * (u' : FF) := rfl
    rw [← this, huu']
    exact V.evalAt_one
  have hune : V.evalAt (u : FF) ≠ 0 := left_ne_zero_of_mul_eq_one hu1
  have key := congrArg (fun z : ↥(R.nodeIntegersOver K w) => V.evalAt (z : FF)) hxy
  beta_reduce at key
  have hcx : ((c.x * c.y : ↥(R.nodeIntegersOver K w)) : FF) = (c.x : FF) * (c.y : FF) := rfl
  have hcr : ((R.nodeConst K w ϖ ^ E * u : ↥(R.nodeIntegersOver K w)) : FF)
      = algebraMap Qb FF ((ϖ : Qb) ^ E) * (u : FF) := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, R.coe_nodeConst, map_pow]
  rw [hcx, hcr, V.evalAt_mul hVr hxO hyO,
    V.evalAt_mul hVr (V.algebraMap_mem' _) huO, V.evalAt_algebraMap] at key
  have hne : V.evalAt (c.x : FF) * V.evalAt (c.y : FF) ≠ 0 := by
    rw [key]
    exact mul_ne_zero (pow_ne_zero _ hϖ0) hune
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

theorem valuation_evalAt_eq_one {w : Place k (modularFunctionFieldC k N)}
    (hvalA : R.ValueIntegralityLaw w) {f : FF} (hf0 : f ≠ 0)
    (hf : f ∈ R.nodeIntegers w) (hf' : f⁻¹ ∈ R.nodeIntegers w)
    (V : Place Qb FF) (hV : P.reduceFst V = w) (hVr : V.IsRational) :
    A.valuation (V.evalAt f) = 1 := by
  have hfO : f ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hf hV
  have hf'O : f⁻¹ ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hf' hV
  have h1 : V.evalAt f * V.evalAt f⁻¹ = 1 := by
    rw [← V.evalAt_mul hVr hfO hf'O, mul_inv_cancel₀ hf0]
    exact V.evalAt_one
  have ha : V.evalAt f ∈ A := hvalA f hf V hV
  have hb : V.evalAt f⁻¹ ∈ A := hvalA f⁻¹ hf' V hV
  have hva : A.valuation (V.evalAt f) ≤ 1 := (A.valuation_le_one_iff _).mpr ha
  have hvb : A.valuation (V.evalAt f⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr hb
  have hprod : A.valuation (V.evalAt f) * A.valuation (V.evalAt f⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  refine le_antisymm hva ?_
  calc (1 : A.ValueGroup) = A.valuation (V.evalAt f) * A.valuation (V.evalAt f⁻¹) := hprod.symm
    _ ≤ A.valuation (V.evalAt f) * 1 := mul_le_mul_right hvb _
    _ = A.valuation (V.evalAt f) := mul_one _

theorem residue_ne_zero_of_residue₁_ne_zero {f : FF} (h₁ : f ∈ R.R₁.integers)
    (h : R.residue₁ ⟨f, h₁⟩ ≠ 0) : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := by
  intro h0
  apply h
  rw [PlaceSpecialization.ProlongationTuple.residue₁_apply, h0, map_zero]

theorem div_data {y : Place k (modularFunctionFieldC k N)} {g h : FF}
    (hg1 : g ∈ R.R₁.integers) (hh1 : h ∈ R.R₁.integers)
    (hgres : R.residue₁ ⟨g, hg1⟩ ≠ 0) (hhres : R.residue₁ ⟨h, hh1⟩ ≠ 0)
    (hord : y.ord (R.residue₁ ⟨g, hg1⟩ : ↥(modularFunctionFieldC k N))
      = y.ord (R.residue₁ ⟨h, hh1⟩ : ↥(modularFunctionFieldC k N)))
    (hgV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : g ∈ V.toValuationSubring, IsUnit (⟨g, hm⟩ : V.toValuationSubring))
    (hhV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : h ∈ V.toValuationSubring, IsUnit (⟨h, hm⟩ : V.toValuationSubring)) :
    ∃ hd1 : g / h ∈ R.R₁.integers,
      R.residue₁ ⟨g / h, hd1⟩ ≠ 0 ∧
      y.ord (R.residue₁ ⟨g / h, hd1⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (∀ V : Place Qb FF, P.reduceFst V = y → g / h ∈ V.toValuationSubring) := by
  have hg0 : g ≠ 0 := by
    rintro rfl; apply hgres
    have : (⟨(0 : FF), hg1⟩ : ↥R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hh0 : h ≠ 0 := by
    rintro rfl; apply hhres
    have : (⟨(0 : FF), hh1⟩ : ↥R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hhu : IsUnit (⟨h, hh1⟩ : ↥R.R₁.integers) :=
    R.R₁.isUnit_of_residue_ne_zero (residue_ne_zero_of_residue₁_ne_zero R hh1 hhres)
  have hhinv : h⁻¹ ∈ R.R₁.integers := inv_mem_of_isUnit hh1 hhu
  have hd1 : g / h ∈ R.R₁.integers := by
    rw [div_eq_mul_inv]; exact mul_mem hg1 hhinv
  have hmul : (⟨g / h, hd1⟩ : ↥R.R₁.integers) * ⟨h, hh1⟩ = ⟨g, hg1⟩ :=
    Subtype.ext (div_mul_cancel₀ g hh0)
  have hres_mul : R.residue₁ ⟨g / h, hd1⟩ * R.residue₁ ⟨h, hh1⟩ = R.residue₁ ⟨g, hg1⟩ := by
    rw [← map_mul, hmul]
  have hres_eq : R.residue₁ ⟨g / h, hd1⟩ = R.residue₁ ⟨g, hg1⟩ / R.residue₁ ⟨h, hh1⟩ := by
    rw [eq_div_iff hhres, hres_mul]
  refine ⟨hd1, ?_, ?_, ?_⟩
  · rw [hres_eq]; exact div_ne_zero hgres hhres
  · rw [hres_eq, div_eq_mul_inv, y.ord_mul hgres (inv_ne_zero hhres), y.ord_inv, hord]
    ring
  · intro V hV
    obtain ⟨hgm, _⟩ := hgV V hV
    obtain ⟨hhm, hhuV⟩ := hhV V hV
    rw [div_eq_mul_inv]
    exact mul_mem hgm (inv_mem_of_isUnit hhm hhuV)

theorem inv_mem_integersSnd_of [PerfectField k]
    {W : Finset (Place k (modularFunctionFieldC k N))} (hreg : R.RegularityLaw W)
    {y : Place k (modularFunctionFieldC k N)} (hy : y ∈ W) {ψ : FF}
    (h1 : ψ ∈ R.R₁.integers) (h2 : ψ ∈ R.R₂.integers)
    (hres : R.residue₁ ⟨ψ, h1⟩ ≠ 0)
    (hord : y.ord (R.residue₁ ⟨ψ, h1⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (hV : ∀ V : Place Qb FF, P.reduceFst V = y → ψ ∈ V.toValuationSubring) :
    ψ⁻¹ ∈ R.R₂.integers := by
  obtain ⟨c, hc1, hc2⟩ := hreg.2 ψ h1 h2 (smulNodePair (arithFrobC q k N) y)
    (smulNodePair_mem_nodePairsOfPlaces _ hy) (fun V hVy => V.ord_nonneg_of_mem (hV V hVy))
  have hc0 : c ≠ 0 := HasValue.ne_zero_of_ord_eq_zero y hc1 hres hord
  have hres2 : (R.residue₂ ⟨ψ, h2⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := hc2.ne_zero hc0
  have hres2' : R.R₂.residue ⟨ψ, h2⟩ ≠ 0 := by
    intro h0; apply hres2
    rw [PlaceSpecialization.ProlongationTuple.residue₂_apply, h0, map_zero]
  exact inv_mem_of_isUnit h2 (R.R₂.isUnit_of_residue_ne_zero hres2')

theorem div_mem_nodeIntegers [PerfectField k]
    {W : Finset (Place k (modularFunctionFieldC k N))} (hreg : R.RegularityLaw W)
    {y : Place k (modularFunctionFieldC k N)} (hy : y ∈ W) {g h : FF}
    (hg1 : g ∈ R.R₁.integers) (hh1 : h ∈ R.R₁.integers)
    (hgres : R.residue₁ ⟨g, hg1⟩ ≠ 0) (hhres : R.residue₁ ⟨h, hh1⟩ ≠ 0)
    (hord : y.ord (R.residue₁ ⟨g, hg1⟩ : ↥(modularFunctionFieldC k N))
      = y.ord (R.residue₁ ⟨h, hh1⟩ : ↥(modularFunctionFieldC k N)))
    (hgV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : g ∈ V.toValuationSubring, IsUnit (⟨g, hm⟩ : V.toValuationSubring))
    (hhV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : h ∈ V.toValuationSubring, IsUnit (⟨h, hm⟩ : V.toValuationSubring)) :
    g / h ∈ R.nodeIntegers y ∧ h / g ∈ R.nodeIntegers y := by
  obtain ⟨hd1, hdres, hdord, hdV⟩ := div_data R hg1 hh1 hgres hhres hord hgV hhV
  obtain ⟨hd1', hdres', hdord', hdV'⟩ := div_data R hh1 hg1 hhres hgres hord.symm hhV hgV
  have key : g / h ∈ R.R₂.integers ∧ h / g ∈ R.R₂.integers := by
    rcases R.R₂.integers.mem_or_inv_mem (g / h) with hA | hB
    · refine ⟨hA, ?_⟩
      rw [← inv_div]
      exact inv_mem_integersSnd_of R hreg hy hd1 hA hdres hdord hdV
    · rw [inv_div] at hB
      refine ⟨?_, hB⟩
      rw [← inv_div]
      exact inv_mem_integersSnd_of R hreg hy hd1' hB hdres' hdord' hdV'
  exact ⟨⟨hd1, key.1, hdV⟩, ⟨hd1', key.2, hdV'⟩⟩

theorem valuation_evalAt_eq_pow [PerfectField k]
    {W : Finset (Place k (modularFunctionFieldC k N))} (hreg : R.RegularityLaw W)
    {y : Place k (modularFunctionFieldC k N)} (hy : y ∈ W) (hvalA : R.ValueIntegralityLaw y)
    {g yy : FF} {e : ℕ} (hg1 : g ∈ R.R₁.integers) (hyy1 : yy ∈ R.R₁.integers)
    (hgres : R.residue₁ ⟨g, hg1⟩ ≠ 0) (hyres : R.residue₁ ⟨yy, hyy1⟩ ≠ 0)
    (hord : y.ord (R.residue₁ ⟨g, hg1⟩ : ↥(modularFunctionFieldC k N)) = e)
    (hyord : y.ord (R.residue₁ ⟨yy, hyy1⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hgV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : g ∈ V.toValuationSubring, IsUnit (⟨g, hm⟩ : V.toValuationSubring))
    (hyyV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : yy ∈ V.toValuationSubring, IsUnit (⟨yy, hm⟩ : V.toValuationSubring))
    (V : Place Qb FF) (hV : P.reduceFst V = y) (hVr : V.IsRational) :
    A.valuation (V.evalAt g) = A.valuation (V.evalAt yy) ^ e := by
  have hh1 : yy ^ e ∈ R.R₁.integers := pow_mem hyy1 e
  have hres_h : R.residue₁ ⟨yy ^ e, hh1⟩ = (R.residue₁ ⟨yy, hyy1⟩) ^ e := by
    rw [← map_pow]; rfl
  have hord_h : y.ord (R.residue₁ ⟨yy ^ e, hh1⟩ : ↥(modularFunctionFieldC k N)) = e := by
    rw [hres_h, ← zpow_natCast, Place.ord_zpow, hyord, mul_one]
  have hhres : R.residue₁ ⟨yy ^ e, hh1⟩ ≠ 0 := by
    rw [hres_h]; exact pow_ne_zero _ hyres
  have hhV : ∀ V : Place Qb FF, P.reduceFst V = y →
      ∃ hm : yy ^ e ∈ V.toValuationSubring, IsUnit (⟨yy ^ e, hm⟩ : V.toValuationSubring) := by
    intro V hV
    obtain ⟨hm, hu⟩ := hyyV V hV
    refine ⟨pow_mem hm e, ?_⟩
    have : (⟨yy ^ e, pow_mem hm e⟩ : V.toValuationSubring) = ⟨yy, hm⟩ ^ e := rfl
    rw [this]; exact hu.pow e
  obtain ⟨hφ, hφ'⟩ :=
    div_mem_nodeIntegers R hreg hy hg1 hh1 hgres hhres (hord.trans hord_h.symm) hgV hhV
  have hg0 : g ≠ 0 := by
    rintro rfl; apply hgres
    have : (⟨(0 : FF), hg1⟩ : ↥R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hyy0 : yy ≠ 0 := by
    rintro rfl; apply hyres
    have : (⟨(0 : FF), hyy1⟩ : ↥R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hh0 : yy ^ e ≠ 0 := pow_ne_zero _ hyy0
  have hunit : A.valuation (V.evalAt (g / yy ^ e)) = 1 :=
    valuation_evalAt_eq_one R hvalA (div_ne_zero hg0 hh0) hφ (by rw [inv_div]; exact hφ') V hV hVr
  obtain ⟨hyO, _⟩ := hyyV V hV
  have hdO : g / yy ^ e ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hφ hV
  have : g = g / yy ^ e * yy ^ e := (div_mul_cancel₀ g hh0).symm
  rw [this, V.evalAt_mul hVr hdO (pow_mem hyO e), map_mul, hunit, one_mul, evalAt_pow V hVr hyO, map_pow]

end NodeRing

end YDepthSubstAux

namespace RedFstSubstAux

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem restrictAlong_of_forall_eq (φ : F →ₐ[K] F) (hid : ∀ x, φ x = x)
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F) : w.restrictAlong φ hφ = w := by
  apply Place.ext
  ext x
  change x ∈ w.toValuationSubring.comap φ.toRingHom ↔ _
  rw [ValuationSubring.mem_comap]
  change φ x ∈ w.toValuationSubring ↔ _
  rw [hid]

end Along

section Composites

variable (L : Type*) [Field L] [Algebra ℚ L] (N q ℓ : ℕ) [NeZero N] [NeZero q] [NeZero ℓ]

theorem heckeAlphaBar_comp_heckeBetaBar_eq (h : N * q * ℓ ∣ N * ℓ * q) :
    (heckeAlphaBar L (N * ℓ) q).comp (heckeBetaBar L N ℓ) =
      (towerSubstBar L (N * q) ℓ h).comp (heckeAlphaBar L N q) := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  simp only [AlgHom.comp_apply, coe_heckeAlphaBar, coe_towerSubstBar, coe_heckeBetaBar]

end Composites

end RedFstSubstAux

open RedFstSubstAux in

theorem YDepthSubstAux.reduceFst_restrictAlong_towerSubstBar_eq_of_reduceFst_eq_of_mem_ssPlaces
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (_hmodel : R.IsModel) (_hO : R.OrderLawFixed),
      ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ) (_hmodelᵣ : Rᵣ.IsModel) (_hOᵣ : Rᵣ.OrderLawFixed)
          (hι : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)).toRingHom.IsIntegral)
          (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ)
          (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
          (y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
          (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ)))
          (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)),
          w ∈ ssPlaces q N (ResidueField A) →
          y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = y →
          y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC = w →
          ∀ (V : Place (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q)))),
            Pᵣ.reduceFst V = y →
            P.reduceFst (V.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) = w := by
  intro data hKr hα hβ P R hmodel hO ℓ hℓq hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hι hβC hroof hroofι y₁ y w hw hy₁y hy₁w
    V hVy

  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
  haveI hℓF : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hqNℓ : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq ((Nat.prime_dvd_prime_iff_eq hq ℓ.2).mp h2).symm
  have hNqℓ_dvd : N * q * ℓ ∣ N * ℓ * q := dvd_of_eq (Nat.mul_right_comm N q ℓ)

  have hRoofEq : charLDegeneracyRoof (ResidueField A) N ℓ = modularFunctionFieldC (ResidueField A) (N * ℓ) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul (ResidueField A) q N ℓ hqNℓ).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q (N * ℓ) hqNℓ).symm
  have hroof' : charLDegeneracyRoof (ResidueField A) N ℓ ≤ modularFunctionFieldC (ResidueField A) (N * ℓ) :=
    le_of_eq hRoofEq
  have hι'_surj : Function.Surjective (IntermediateField.inclusion hroof') := by
    intro x
    exact ⟨⟨x.1, hroof x.2⟩, Subtype.ext rfl⟩
  have hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ hι'_surj
  have hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral :=
    heckeAlphaCIntegral_unconditional (ResidueField A) N ℓ

  have hφ₀ : ((IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hαC hι'
  have hφ₁ : ((IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hβC hι'
  obtain ⟨φ, hφ0, hφ1⟩ : ∃ φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) N) →ₐ[ResidueField A]
      ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))),
      φ 0 = (IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) N ℓ) ∧
      φ 1 = (IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ) := ⟨![_, _], rfl, rfl⟩
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral :=
    Fin.forall_fin_two.mpr ⟨by rw [hφ0]; exact hφ₀, by rw [hφ1]; exact hφ₁⟩
  have hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) :
      LaurentSeries (ResidueField A)) = x := by
    intro x
    rw [hφ0]
    exact coe_heckeAlphaC (ResidueField A) N ℓ x
  have hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) :
      LaurentSeries (ResidueField A)) = qExpand (ResidueField A) ℓ x := by
    intro x
    rw [hφ1]
    exact coe_heckeBetaC (ResidueField A) N ℓ x

  have hδ₀ : (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ).toRingHom.IsIntegral :=
    towerInclBar_isIntegral (AlgebraicClosure ℚ) (dvd_mul_right N (ℓ : ℕ))
  have hδ₁ : (heckeBetaBar (AlgebraicClosure ℚ) N ℓ).toRingHom.IsIntegral := by
    rw [heckeBetaBar_eq_towerSubstBar]
    exact towerSubstBar_isIntegral (AlgebraicClosure ℚ) ℓ dvd_rfl
  obtain ⟨δ, hδ0, hδ1⟩ : ∃ δ : Fin 2 → (↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
      ↥(modularFunctionFieldBar (N * ℓ))),
      δ 0 = heckeAlphaBar (AlgebraicClosure ℚ) N ℓ ∧ δ 1 = heckeBetaBar (AlgebraicClosure ℚ) N ℓ :=
    ⟨![_, _], rfl, rfl⟩
  have hδ : ∀ i, (δ i).toRingHom.IsIntegral :=
    Fin.forall_fin_two.mpr ⟨by rw [hδ0]; exact hδ₀, by rw [hδ1]; exact hδ₁⟩
  have hδα : ∀ x, ((δ 0 x : ↥(modularFunctionFieldBar (N * ℓ))) : LaurentSeries (AlgebraicClosure ℚ)) = x := by
    intro x
    rw [hδ0]
    exact coe_heckeAlphaBar N ℓ x
  have hδβ : ∀ x, ((δ 1 x : ↥(modularFunctionFieldBar (N * ℓ))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) ℓ x := by
    intro x
    rw [hδ1]
    exact coe_heckeBetaBar N ℓ x

  obtain ⟨v, hv⟩ : ∃ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ)),
      v = V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hαᵣ := ⟨_, rfl⟩
  have hredᵣ : Pᵣ.reduceFst V = Pᵣ.sp v := by
    rw [hv]
    rfl
  have hv₁ : v.restrictAlong (δ 1) (hδ 1) =
      (V.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ hNqℓ_dvd) hι).restrictAlong
        (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα := by
    have h1 := Place.restrictAlong_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hδ₁ hαᵣ (RingHom.IsIntegral.trans _ _ hδ₁ hαᵣ) V
    have h2 := Place.restrictAlong_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ hNqℓ_dvd) hα hι (RingHom.IsIntegral.trans _ _ hα hι) V
    have h0 : v.restrictAlong (δ 1) (hδ 1) =
        (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hαᵣ).restrictAlong
          (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hδ₁ := by
      subst hv
      exact Place.restrictAlong_congr hδ1 _ _ _
    rw [h0, h1, h2]
    exact Place.restrictAlong_congr
      (heckeAlphaBar_comp_heckeBetaBar_eq (AlgebraicClosure ℚ) N q ℓ hNqℓ_dvd) _ _ _
  have hred₁ : P.reduceFst (V.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ hNqℓ_dvd) hι) =
      P.sp (v.restrictAlong (δ 1) (hδ 1)) := by
    rw [hv₁]
    rfl

  have hyv : Pᵣ.sp v = y := hredᵣ.symm.trans hVy
  have hy₁' : y.restrictAlong (IntermediateField.inclusion hroof') hι' = y₁ := by
    rw [← hy₁y, Place.restrictAlong_restrictAlong (IntermediateField.inclusion hroof')
      (IntermediateField.inclusion hroof) hι' hroofι (RingHom.IsIntegral.trans _ _ hι' hroofι)]
    exact restrictAlong_of_forall_eq _ (fun x => Subtype.ext rfl) _ _
  have hu : (Pᵣ.sp v).restrictAlong (φ 1) (hφ 1) = w :=
    calc (Pᵣ.sp v).restrictAlong (φ 1) (hφ 1)
        = y.restrictAlong ((IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ)) hφ₁ := by
          rw [hyv]; exact Place.restrictAlong_congr hφ1 _ _ _
      _ = (y.restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
            (heckeBetaC (ResidueField A) N ℓ) hβC :=
          (Place.restrictAlong_restrictAlong (heckeBetaC (ResidueField A) N ℓ)
            (IntermediateField.inclusion hroof') hβC hι' hφ₁ y).symm
      _ = w := by rw [hy₁', hy₁w]

  have hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField A) N data hKr ((Pᵣ.sp v).restrictAlong (φ 1) (hφ 1))) =
        (Pᵣ.sp v).restrictAlong (φ 1) (hφ 1) := by
    rw [hu]
    exact PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P _ hw
  have haff : IsAffineGeomPlace (ResidueField A) N ((Pᵣ.sp v).restrictAlong (φ 1) (hφ 1)) := by
    rw [hu]
    exact ((mem_ssPlaces_iff (q := q) (N := N) (K := ResidueField A)).mp hw).2.1
  have hC := PlaceSpecialization.sp_restrictAlong_eq_restrictAlong_sp_of_isModel_of_fixed_of_isAffineGeomPlace N ℓ q
    ℓ.2 hq hℓq hqN A hA data hKr hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ data hKr hα hβ P R hmodel hO δ hδ hδα hδβ φ hφ hφα hφβ
  have hcompat₁ : P.sp (v.restrictAlong (δ 1) (hδ 1)) = (Pᵣ.sp v).restrictAlong (φ 1) (hφ 1) :=
    hC 1 v hfix haff
  exact hred₁.trans (hcompat₁.trans hu)

open YDepthSubstAux in
theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N) (hq5 : 5 ≤ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
      (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
      (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
      (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict (IsLocalRing.residue A) (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
      (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))),
        1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (ϖ w) ^ E * u),
        ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (Wᵣ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))))
          (hWᵣ : ∀ w, w ∈ Wᵣ ↔ w ∈ ssPlaces q (N * ℓ) (ResidueField A))
          (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ) (hmodelᵣ : Rᵣ.IsModel) (hOᵣ : Rᵣ.OrderLawFixed)
          (hregᵣ : Rᵣ.RegularityLaw Wᵣ) (hvalᵣ : Rᵣ.NodeValueLaw Wᵣ)
          (Ksᵣ : ↥Wᵣ → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥Wᵣ, FiniteDimensional ℚ (Ksᵣ w)]
          (csᵣ : ∀ w : ↥Wᵣ, Rᵣ.NodeCoordinates (Ksᵣ w) (w : Place (ResidueField A) (modularFunctionFieldC
              (ResidueField A) (N * ℓ))))
          (ϖᵣ : ∀ w : ↥Wᵣ, ↥(NodeLocalized.coeffSubring A (Ksᵣ w)))
          (hϖᵣ : ∀ (w : ↥Wᵣ) (d : ↥(NodeLocalized.coeffSubring A (Ksᵣ w))), NodeLocalized.redRestrict
              (IsLocalRing.residue A) (Ksᵣ w) d = 0 ↔ ∃ d', d = ϖᵣ w * d')
          (hvalAᵣ : ∀ w : ↥Wᵣ, Rᵣ.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField
              A) (N * ℓ))))
          (hxyᵣ : ∀ w : ↥Wᵣ, ∃ (E : ℕ) (u : ↥(Rᵣ.nodeIntegersOver (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))))),
          1 ≤ E ∧ IsUnit u ∧ (csᵣ w).x * (csᵣ w).y = Rᵣ.nodeConst (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) (ϖᵣ w) ^ E * u),
        ∀ (hι : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)).toRingHom.IsIntegral)
          (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ)
          (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
          (y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
          (y : ↥Wᵣ) (w : ↥W),
          y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = (y : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) →
          y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC = (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N)) →
          ∀ (V' : Place (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q)))),
            Pᵣ.reduceFst V' = y →
            P.reduceFst (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) = w →
            (cs w).yDepth (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι)
                = (csᵣ y).yDepth V' ^ y₁.ramificationIndexAlong (heckeBetaC (ResidueField A) N ℓ) ∧
              (P.IsStrictFst (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) ↔ Pᵣ.IsStrictFst V') := by
  intro W hW data hKr hα hβ P R hmodel hO hreg hval Ks _iKs cs ϖ hϖ hvalA hxy ℓ hℓ Wᵣ hWᵣ hαᵣ hβᵣ Pᵣ Rᵣ
    hmodelᵣ hOᵣ hregᵣ hvalᵣ Ksᵣ _iKsᵣ csᵣ ϖᵣ hϖᵣ hvalAᵣ hxyᵣ hι hβC hroof hroofι y₁ y w hy₁y hy₁w V' hV'y hV'w

  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)

  have hqNℓ : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓ ((Nat.prime_dvd_prime_iff_eq hq ℓ.2).mp h2).symm

  haveI hcurve₁ : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull _ _
  haveI hcurve₂ : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull _ _
  have hrat₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational :=
    fun V => (Place.isRational_iff_deg_eq_one V).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed V)
  have hrat₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)), V.IsRational :=
    fun V => (Place.isRational_iff_deg_eq_one V).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed V)

  have hϖ0 : ((ϖ w : ↥(NodeLocalized.coeffSubring A (Ks w))) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    obtain ⟨d', hd'⟩ := (hϖ w (q : ↥(NodeLocalized.coeffSubring A (Ks w)))).mp
      (by rw [map_natCast]; exact CharP.cast_eq_zero _ q)
    have h1 : (((q : ↥(NodeLocalized.coeffSubring A (Ks w))) : ↥(NodeLocalized.coeffSubring A (Ks w)))
        : AlgebraicClosure ℚ) = 0 := by
      rw [hd', Subring.coe_mul, h0, zero_mul]
    rw [Subring.coe_natCast] at h1
    exact (NeZero.ne q) (Nat.cast_eq_zero.mp h1)
  have hϖᵣ0 : ((ϖᵣ y : ↥(NodeLocalized.coeffSubring A (Ksᵣ y))) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    obtain ⟨d', hd'⟩ := (hϖᵣ y (q : ↥(NodeLocalized.coeffSubring A (Ksᵣ y)))).mp
      (by rw [map_natCast]; exact CharP.cast_eq_zero _ q)
    have h1 : (((q : ↥(NodeLocalized.coeffSubring A (Ksᵣ y))) : ↥(NodeLocalized.coeffSubring A (Ksᵣ y)))
        : AlgebraicClosure ℚ) = 0 := by
      rw [hd', Subring.coe_mul, h0, zero_mul]
    rw [Subring.coe_natCast] at h1
    exact (NeZero.ne q) (Nat.cast_eq_zero.mp h1)

  have hC1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)),
      Pᵣ.reduceFst V = y →
        P.reduceFst (V.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
          (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) = w := fun V hV =>
    YDepthSubstAux.reduceFst_restrictAlong_towerSubstBar_eq_of_reduceFst_eq_of_mem_ssPlaces N q hq hqN A hA
      data hKr hα hβ P R hmodel hO ℓ hℓ hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hι hβC hroof hroofι y₁ y w
      ((hW w).mp w.2) hy₁y hy₁w V hV

  obtain ⟨hg1, hgcoe⟩ :=
    PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq R (ℓ : ℕ) Rᵣ
      ((cs w).y : ↥(modularFunctionFieldBar (N * q))) (cs w).y.2.1.1

  have hr1 : (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).ord
      (R.residue₁ ⟨((cs w).y : ↥(modularFunctionFieldBar (N * q))), (cs w).y.2.1.1⟩
        : ↥(modularFunctionFieldC (ResidueField A) N)) = 1 := by
    have := (cs w).y_fst
    rwa [PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply] at this
  have hyres1 : (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))).ord
      (Rᵣ.residue₁ ⟨((csᵣ y).y : ↥(modularFunctionFieldBar (N * ℓ * q))), (csᵣ y).y.2.1.1⟩
        : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) = 1 := by
    have := (csᵣ y).y_fst
    rwa [PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply] at this
  have hyres_ne : (Rᵣ.residue₁ ⟨((csᵣ y).y : ↥(modularFunctionFieldBar (N * ℓ * q))), (csᵣ y).y.2.1.1⟩
      : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) ≠ 0 := by
    have := (csᵣ y).nodeResidue₁_y_ne_zero
    rwa [PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply] at this

  have hroofeq : charLDegeneracyRoof (ResidueField A) N ℓ = modularFunctionFieldC (ResidueField A) (N * ℓ) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul (ResidueField A) q N ℓ hqNℓ).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q (N * ℓ) hqNℓ).symm
  have hsurj : Function.Surjective (IntermediateField.inclusion hroof) := by
    intro z
    have hz : (z : LaurentSeries (ResidueField A)) ∈ modularFunctionFieldC (ResidueField A) (N * ℓ) := by
      rw [← hroofeq]; exact z.2
    exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩

  have hincl_eq : IntermediateField.inclusion hroof (Rᵣ.residue₁ ⟨_, hg1⟩)
      = heckeBetaC (ResidueField A) N ℓ
          (R.residue₁ ⟨((cs w).y : ↥(modularFunctionFieldBar (N * q))), (cs w).y.2.1.1⟩) := by
    apply Subtype.ext
    rw [IntermediateField.coe_inclusion, coe_heckeBetaC, ← hgcoe]
  have hord_g := ord_eq_ramificationIndexAlong_mul_ord (IntermediateField.inclusion hroof) hroofι hsurj
    (heckeBetaC (ResidueField A) N ℓ) hβC y₁ hy₁y hy₁w hincl_eq
  rw [hr1, mul_one] at hord_g
  have hgres_ne : (Rᵣ.residue₁ ⟨_, hg1⟩ : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hord_g
    have he1 := Place.one_le_ramificationIndexAlong _ hβC y₁
    have h3 : y₁.ramificationIndexAlong (heckeBetaC (ResidueField A) N ℓ) = 0 := by exact_mod_cast hord_g.symm
    rw [h3] at he1
    exact Nat.not_succ_le_zero 0 he1

  have hgV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)),
      Pᵣ.reduceFst V = y →
        ∃ hm : towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
            (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)
            ((cs w).y : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring,
          IsUnit (⟨_, hm⟩ : V.toValuationSubring) := by
    intro V hV
    have hw' := hC1 V hV
    exact exists_isUnit_map_of_evalAt_ne_zero _ hι V (hrat₂ V) (hrat₁ _)
      (R.mem_toValuationSubring_of_mem_nodeIntegers (cs w).y.2.1 hw')
      (evalAt_coord_ne_zero R (cs w) hϖ0 (hxy w) _ hw' (hrat₁ _)).2
  have hyyV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)),
      Pᵣ.reduceFst V = y →
        ∃ hm : ((csᵣ y).y : ↥(modularFunctionFieldBar (N * ℓ * q))) ∈ V.toValuationSubring,
          IsUnit (⟨_, hm⟩ : V.toValuationSubring) := fun V hV =>
    ⟨Rᵣ.mem_toValuationSubring_of_mem_nodeIntegers (csᵣ y).y.2.1 hV,
      isUnit_of_evalAt_ne_zero V (hrat₂ V) _ (evalAt_coord_ne_zero Rᵣ (csᵣ y) hϖᵣ0 (hxyᵣ y) V hV (hrat₂ V)).2⟩

  have hval_g := valuation_evalAt_eq_pow Rᵣ hregᵣ y.2 (hvalAᵣ y) hg1 (csᵣ y).y.2.1.1 hgres_ne hyres_ne hord_g
    hyres1 hgV hyyV V' hV'y (hrat₂ V')
  refine ⟨?_, ?_⟩
  ·
    show A.valuation (Place.evalAt _ ((cs w).y : ↥(modularFunctionFieldBar (N * q))))
      = A.valuation (V'.evalAt ((csᵣ y).y : ↥(modularFunctionFieldBar (N * ℓ * q)))) ^ _
    rw [evalAt_restrictAlong _ hι V' (hrat₂ V') (hrat₁ _)
      (R.mem_toValuationSubring_of_mem_nodeIntegers (cs w).y.2.1 hV'w)]
    exact hval_g
  ·
    have hfixw := PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ((hW w).mp w.2)
    have hfixy := PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqNℓ Pᵣ
      (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))) ((hWᵣ y).mp y.2)
    refine iff_of_false (fun h => h.2 ?_) (fun h => h.2 ?_)
    · rw [hV'w]; exact hfixw
    · rw [hV'y]; exact hfixy

end S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC (solution)
