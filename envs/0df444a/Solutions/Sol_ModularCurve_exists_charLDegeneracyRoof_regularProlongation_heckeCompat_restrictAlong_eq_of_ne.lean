-- Prove2me | solution 1 for ModularCurve.exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9578bdb8-57e4-5987-9bc7-8fc01169cf8f

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_jZero_zsmul_surjective
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option Elab.async false

namespace PlaceCompat

section FinsuppKit

variable {α β : Type*}

theorem mapDomain_eq_single_of_forall_eq (f : α → β) (x : α →₀ ℤ) (b : β)
    (h : ∀ a ∈ x.support, f a = b) :
    Finsupp.mapDomain f x = Finsupp.single b (x.sum fun _ m => m) := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

theorem sum_mapDomain_id (f : α → β) (x : α →₀ ℤ) :
    ((Finsupp.mapDomain f x).sum fun _ m => m) = x.sum fun _ m => m :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem mapDomain_apply_eq_sum [DecidableEq β] (f : α → β) (x : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain f x b = ∑ a ∈ x.support, if f a = b then x a else 0 := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mapDomain_nonneg (f : α → β) {x : α →₀ ℤ} (hx : ∀ a, 0 ≤ x a) (b : β) :
    0 ≤ Finsupp.mapDomain f x b := by
  classical
  rw [mapDomain_apply_eq_sum]
  have hterm : ∀ a, 0 ≤ (if f a = b then x a else 0) := fun a => by
    split_ifs
    · exact hx a
    · exact le_rfl
  exact Finset.sum_nonneg fun a _ => hterm a

theorem le_mapDomain_apply (f : α → β) {x : α →₀ ℤ} (hx : ∀ a, 0 ≤ x a) (a : α) :
    x a ≤ Finsupp.mapDomain f x (f a) := by
  classical
  rw [mapDomain_apply_eq_sum]
  have hterm : ∀ a', 0 ≤ (if f a' = f a then x a' else 0) := fun a' => by
    split_ifs
    · exact hx a'
    · exact le_rfl
  by_cases ha : a ∈ x.support
  · have h1 : x a = (if f a = f a then x a else 0) := by rw [if_pos rfl]
    rw [h1]
    exact Finset.single_le_sum (f := fun a' => if f a' = f a then x a' else 0)
      (fun a' _ => hterm a') ha
  · have h0 : x a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    rw [h0]
    exact Finset.sum_nonneg fun a' _ => hterm a'

theorem eq_zero_of_nonneg_of_sum_eq_zero {x : β →₀ ℤ} (hx : ∀ b, 0 ≤ x b)
    (h0 : (x.sum fun _ m => m) = 0) : x = 0 := by
  simp only [Finsupp.sum] at h0
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hx b)).mp h0
  ext b
  by_cases hb : b ∈ x.support
  · exact h b hb
  · simpa [Finsupp.mem_support_iff] using hb

theorem exists_pos_of_sum_eq_zero_of_neg {x : β →₀ ℤ} (h0 : (x.sum fun _ m => m) = 0)
    {b₀ : β} (hb₀ : x b₀ < 0) : ∃ b, 0 < x b := by
  classical
  by_contra hcon
  push Not at hcon
  have hmem : b₀ ∈ x.support := Finsupp.mem_support_iff.mpr hb₀.ne
  have h0' : ∑ b ∈ x.support, x b = 0 := by simpa [Finsupp.sum] using h0
  rw [← Finset.add_sum_erase x.support (fun b => x b) hmem] at h0'
  have hle : ∑ b ∈ x.support.erase b₀, x b ≤ 0 := Finset.sum_nonpos fun b _ => hcon b
  linarith

end FinsuppKit

section DegreeKit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ m => m := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D hv hn ih =>
    rw [map_add, Divisor.degree_single, hdeg v, Nat.cast_one, mul_one, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl]

theorem exists_ord_eq_one (v : Place K F) : ∃ x : F, v.ord x = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨(π : F), v.ord_coe_irreducible hπ⟩

end DegreeKit

section Rigid

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb]

theorem apply_eq_zero_of_mem_degZero (Ψ : Divisor K F →+ Divisor k Fb)
    (hΨ : ∀ D : Divisor K F, D.IsPrincipal → Ψ D = 0)
    (hdiv : ∀ m : ℤ, m ≠ 0 → Function.Surjective fun x : Pic0 K F => m • x)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Ψ D = 0 := by
  ext Q
  rw [Finsupp.zero_apply]

  have hm0 : (|Ψ D Q| + 1 : ℤ) ≠ 0 := by positivity
  obtain ⟨y, hy⟩ := hdiv (|Ψ D Q| + 1) hm0 (Pic0.mk ⟨D, hD⟩)
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective y

  have hy' : Pic0.mk ((|Ψ D Q| + 1) • E) = Pic0.mk ⟨D, hD⟩ := by
    rw [← hy]
    rfl
  have hprin : -((((|Ψ D Q| + 1) • E : Divisor.degZero (K := K) (F := F)) : Divisor K F))
      + ((⟨D, hD⟩ : Divisor.degZero (K := K) (F := F)) : Divisor K F)
        ∈ Divisor.principal (K := K) (F := F) := by
    have h := (QuotientAddGroup.eq.mp hy')
    rw [AddSubgroup.mem_addSubgroupOf] at h
    exact h
  have hcoe : ((((|Ψ D Q| + 1) • E : Divisor.degZero (K := K) (F := F)) : Divisor K F))
      = (|Ψ D Q| + 1) • (E : Divisor K F) := rfl
  have hΨD : Ψ D = (|Ψ D Q| + 1) • Ψ (E : Divisor K F) := by
    have h0 := hΨ _ hprin
    rw [map_add, map_neg, neg_add_eq_zero, hcoe, map_zsmul] at h0
    exact h0.symm
  have hcQ : Ψ D Q = (|Ψ D Q| + 1) * Ψ (E : Divisor K F) Q := by
    have h := congrArg (fun D' : Divisor k Fb => D' Q) hΨD
    simpa using h

  have hdvd : (|Ψ D Q| + 1) ∣ Ψ D Q := ⟨_, hcQ⟩
  exact Int.eq_zero_of_abs_lt_dvd hdvd (lt_add_one _)

end Rigid

section General

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
variable {Fb Fb' : Type*} [Field Fb] [Field Fb']
variable [Algebra (ResidueField A) Fb] [Algebra (ResidueField A) Fb']

theorem mapDomain_pullbackAlong_eq_pullbackAlong_mapDomain
    [HasPrincipalDivisors L F'] [HasPrincipalDivisors (ResidueField A) Fb']
    (φ : F →ₐ[L] F') (hφ : φ.toRingHom.IsIntegral)
    (φC : Fb →ₐ[ResidueField A] Fb') (hφC : φC.toRingHom.IsIntegral)
    (R : RegularProlongation A F Fb) (R' : RegularProlongation A F' Fb')
    (r : Place L F → Place (ResidueField A) Fb) (r' : Place L F' → Place (ResidueField A) Fb')
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hr' : ∀ f : R'.integers, R'.residue f ≠ 0 → ∀ D : Divisor L F',
      (∀ P, D P = P.ord (f : F')) → ∀ Q, Finsupp.mapDomain r' D Q = Q.ord (R'.residue f))
    (hres : ∀ f : R.integers, ∃ h : φ (f : F) ∈ R'.integers,
      R'.residue ⟨_, h⟩ = φC (R.residue f))
    (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F)) :
    Finsupp.mapDomain r' (Divisor.pullbackAlong φ hφ D)
      = Divisor.pullbackAlong φC hφC (Finsupp.mapDomain r D) := by
  obtain ⟨hmem, hresφ⟩ := hres f
  have hne : R'.residue ⟨φ (f : F), hmem⟩ ≠ 0 := by
    rw [hresφ]
    exact (map_ne_zero_iff _ (φC : Fb →+* Fb').injective).mpr hf
  have hD' : ∀ W, Divisor.pullbackAlong φ hφ D W
      = W.ord (((⟨φ (f : F), hmem⟩ : R'.integers) : F')) := fun W => by
    rw [Divisor.pullbackAlong_apply, hD]
    exact (Place.ord_restrictAlong φ hφ W (f : F)).symm
  ext Y
  rw [hr' ⟨φ (f : F), hmem⟩ hne _ hD' Y, Divisor.pullbackAlong_apply,
    hr f hf D hD (Y.restrictAlong φC hφC), hresφ]
  exact Place.ord_restrictAlong φC hφC Y (R.residue f)

theorem mapDomain_restrictAlong_pullbackAlong
    {k E E' : Type*} [Field k] [Field E] [Field E'] [Algebra k E] [Algebra k E']
    [HasPrincipalDivisors k E']
    (ψ : E →ₐ[k] E') (hψ : ψ.toRingHom.IsIntegral)
    (hdeg1 : ∀ Y : Place k E', Y.deg = 1) (n : ℕ)
    (hdown : ∀ Q : Place k E,
      Divisor.degree (Divisor.pullbackAlong ψ hψ (Finsupp.single Q 1)) = n)
    (D : Divisor k E) :
    Finsupp.mapDomain (Place.restrictAlong ψ hψ) (Divisor.pullbackAlong ψ hψ D) = (n : ℤ) • D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add Q m D hQ hm ih =>
    rw [map_add, Finsupp.mapDomain_add, ih, smul_add]
    congr 1

    have hsupp : ∀ Y ∈ (Divisor.pullbackAlong ψ hψ (Finsupp.single Q m)).support,
        Y.restrictAlong ψ hψ = Q := by
      intro Y hY
      by_contra hne
      rw [Finsupp.mem_support_iff, Divisor.pullbackAlong_apply] at hY
      apply hY
      rw [Finsupp.single_eq_of_ne hne, mul_zero]
    rw [mapDomain_eq_single_of_forall_eq _ _ Q hsupp, ← degree_eq_sum hdeg1,
      show Finsupp.single Q m = m • Finsupp.single Q (1 : ℤ) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_zsmul, map_zsmul, hdown, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_one]
    ring_nf

theorem restrictAlong_placeMap_eq_placeMap_restrictAlong
    [HasPrincipalDivisors L F] [HasPrincipalDivisors L F']
    [HasPrincipalDivisors (ResidueField A) Fb']
    (φ : F →ₐ[L] F') (hφ : φ.toRingHom.IsIntegral)
    (φC : Fb →ₐ[ResidueField A] Fb') (hφC : φC.toRingHom.IsIntegral)
    (R : RegularProlongation A F Fb) (R' : RegularProlongation A F' Fb')
    (r : Place L F → Place (ResidueField A) Fb) (r' : Place L F' → Place (ResidueField A) Fb')
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hr' : ∀ f : R'.integers, R'.residue f ≠ 0 → ∀ D : Divisor L F',
      (∀ P, D P = P.ord (f : F')) → ∀ Q, Finsupp.mapDomain r' D Q = Q.ord (R'.residue f))
    (hres : ∀ f : R.integers, ∃ h : φ (f : F) ∈ R'.integers,
      R'.residue ⟨_, h⟩ = φC (R.residue f))
    (hdegF : ∀ v : Place L F, v.deg = 1) (hdegF' : ∀ W : Place L F', W.deg = 1)
    (hdegFb : ∀ Q : Place (ResidueField A) Fb, Q.deg = 1)
    (hdegFb' : ∀ Y : Place (ResidueField A) Fb', Y.deg = 1)
    (hdiv : ∀ m : ℤ, m ≠ 0 → Function.Surjective fun x : Pic0 L F => m • x)
    (n : ℕ) (hn : 0 < n)
    (hup : ∀ v : Place L F,
      Divisor.degree (Divisor.pullbackAlong φ hφ (Finsupp.single v 1)) = n)
    (hdown : ∀ Q : Place (ResidueField A) Fb,
      Divisor.degree (Divisor.pullbackAlong φC hφC (Finsupp.single Q 1)) = n) :
    ∀ W : Place L F', (r' W).restrictAlong φC hφC = r (W.restrictAlong φ hφ) := by
  have _ := hn
  intro W
  set v₀ := W.restrictAlong φ hφ with hv₀

  let Efun : Divisor L F → Divisor (ResidueField A) Fb := fun D =>
    Finsupp.mapDomain (Place.restrictAlong φC hφC)
      (Finsupp.mapDomain r' (Divisor.pullbackAlong φ hφ D))
  have Efun_add : ∀ D D', Efun (D + D') = Efun D + Efun D' := fun D D' => by
    simp only [Efun, map_add, Finsupp.mapDomain_add]
  let Ψ : Divisor L F →+ Divisor (ResidueField A) Fb :=
    AddMonoidHom.mk' (fun D => Efun D - (n : ℤ) • Finsupp.mapDomain r D) (fun D D' => by
      show Efun (D + D') - (n : ℤ) • Finsupp.mapDomain r (D + D')
        = (Efun D - (n : ℤ) • Finsupp.mapDomain r D) + (Efun D' - (n : ℤ) • Finsupp.mapDomain r D')
      rw [Efun_add, Finsupp.mapDomain_add, smul_add]
      abel)
  have hΨapply : ∀ D, Ψ D = Efun D - (n : ℤ) • Finsupp.mapDomain r D := fun D => rfl

  have hΨp : ∀ D : Divisor L F, D.IsPrincipal → Ψ D = 0 := by
    rintro D ⟨g, hg0, hDg⟩
    obtain ⟨c, hc, hres0⟩ := R.exists_smul_mem g hg0
    have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hres0
    have hDf : ∀ P, D P = P.ord (((⟨c • g, hc⟩ : R.integers) : F)) := fun P => by
      rw [hDg P]
      exact (ConstantReduction.ord_smul P hc0 g).symm
    rw [hΨapply, sub_eq_zero]
    show Finsupp.mapDomain (Place.restrictAlong φC hφC)
        (Finsupp.mapDomain r' (Divisor.pullbackAlong φ hφ D)) = _
    rw [mapDomain_pullbackAlong_eq_pullbackAlong_mapDomain φ hφ φC hφC R R' r r' hr hr' hres
        ⟨c • g, hc⟩ hres0 D hDf,
      mapDomain_restrictAlong_pullbackAlong φC hφC hdegFb' n hdown]

  have hΨ0 : ∀ D ∈ Divisor.degZero (K := L) (F := F), Ψ D = 0 := fun D hD =>
    apply_eq_zero_of_mem_degZero Ψ hΨp hdiv hD
  have hconst : ∀ v, Ψ (Finsupp.single v 1) = Ψ (Finsupp.single v₀ 1) := by
    intro v
    rw [← sub_eq_zero, ← map_sub]
    apply hΨ0
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdegF,
      hdegF, sub_self]
  set ε := Ψ (Finsupp.single v₀ 1) with hε

  have hE : ∀ v, Efun (Finsupp.single v 1) = (n : ℤ) • Finsupp.single (r v) 1 + ε := by
    intro v
    rw [← hconst v, hΨapply, Finsupp.mapDomain_single]
    abel
  have hPnn : ∀ v W', 0 ≤ Divisor.pullbackAlong φ hφ (Finsupp.single v 1) W' := by
    intro v W'
    rw [Divisor.pullbackAlong_apply]
    by_cases h : Place.restrictAlong φ hφ W' = v
    · rw [h, Finsupp.single_eq_same, mul_one]
      exact_mod_cast Nat.zero_le _
    · rw [Finsupp.single_eq_of_ne h, mul_zero]
  have hEnn : ∀ v Q, 0 ≤ Efun (Finsupp.single v 1) Q := fun v Q =>
    mapDomain_nonneg _ (fun Y => mapDomain_nonneg _ (hPnn v) Y) Q
  have hEsum : ∀ v, ((Efun (Finsupp.single v 1)).sum fun _ m => m) = n := by
    intro v
    simp only [Efun]
    rw [sum_mapDomain_id, sum_mapDomain_id, ← degree_eq_sum hdegF', hup]
  have hεsum : (ε.sum fun _ m => m) = 0 := by
    have h1 := hEsum v₀
    rw [hE v₀, ← degree_eq_sum hdegFb, map_add, map_zsmul, Divisor.degree_single, hdegFb,
      degree_eq_sum hdegFb] at h1
    simp only [smul_eq_mul] at h1
    omega

  have hεnn : ∀ Q, 0 ≤ ε Q := by
    by_contra hneg
    push Not at hneg
    obtain ⟨Q₀, hQ₀⟩ := hneg
    have hrconst : ∀ v, r v = Q₀ := by
      intro v
      by_contra hv
      have h := congrArg (fun D : Divisor (ResidueField A) Fb => D Q₀) (hE v)
      simp only [Finsupp.add_apply, Finsupp.smul_apply] at h
      rw [Finsupp.single_eq_of_ne (Ne.symm hv), smul_zero,
        zero_add] at h
      have := hEnn v Q₀
      rw [h] at this
      exact absurd hQ₀ (not_lt.mpr this)
    obtain ⟨Q₁, hQ₁⟩ := exists_pos_of_sum_eq_zero_of_neg hεsum hQ₀
    have hQ10 : Q₁ ≠ Q₀ := by
      rintro rfl
      exact absurd hQ₀ (not_lt.mpr hQ₁.le)

    obtain ⟨x, hx⟩ := exists_ord_eq_one Q₁
    obtain ⟨f, hf⟩ := R.residue_surjective x
    have hf0 : R.residue f ≠ 0 := by
      rw [hf]
      rintro rfl
      rw [Place.ord_zero] at hx
      exact zero_ne_one hx
    have hfF : (f : F) ≠ 0 := by
      intro h0
      apply hf0
      have : f = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (f : F) hfF
    have h1 := hr f hf0 D hD Q₁
    rw [mapDomain_eq_single_of_forall_eq r D Q₀ (fun a _ => hrconst a),
      Finsupp.single_eq_of_ne hQ10, hf, hx] at h1
    exact zero_ne_one h1
  have hε0 : ε = 0 := eq_zero_of_nonneg_of_sum_eq_zero hεnn hεsum

  have hEv := hE v₀
  rw [hε0, add_zero] at hEv
  have he : 0 < Place.ramificationIndexAlong φ W := by
    letI := algebraAlong φ
    haveI := isIntegral_along φ hφ
    exact W.ramificationIndex_pos (F := F)
  have hW : (1 : ℤ) ≤ Efun (Finsupp.single v₀ 1) ((r' W).restrictAlong φC hφC) := by
    calc (1 : ℤ) ≤ Divisor.pullbackAlong φ hφ (Finsupp.single v₀ 1) W := by
          rw [Divisor.pullbackAlong_apply, ← hv₀, Finsupp.single_eq_same, mul_one]
          exact_mod_cast he
      _ ≤ Finsupp.mapDomain r' (Divisor.pullbackAlong φ hφ (Finsupp.single v₀ 1)) (r' W) :=
          le_mapDomain_apply r' (hPnn v₀) W
      _ ≤ Efun (Finsupp.single v₀ 1) ((r' W).restrictAlong φC hφC) :=
          le_mapDomain_apply (Place.restrictAlong φC hφC)
            (fun Y => mapDomain_nonneg _ (hPnn v₀) Y) (r' W)
  by_contra hne
  rw [hEv, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne hne, smul_zero] at hW
  exact absurd hW (by norm_num)

end General

end PlaceCompat

set_option maxHeartbeats 12800000 in
theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N ℓ)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hjN : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
        ∈ R₁.integers,
      R₁.residue ⟨_, h⟩
        = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩) :
    ∃ (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * ℓ))
        (charLDegeneracyRoof (ResidueField ↥A) N ℓ))
      (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))
        → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N ℓ)),
      (∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
          (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * ℓ))) →
        ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f))
      ∧ (∀ f : R₁.integers,
          ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
              ∈ Rℓ.integers,
            Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N ℓ (R₁.residue f))
      ∧ (∀ f : R₁.integers,
          ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N)
              ∈ Rℓ.integers,
            Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N ℓ (R₁.residue f))
      ∧ (∀ v, Divisor.degree
            (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
              (Finsupp.single v 1))
          = Divisor.degree
            (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
              (Finsupp.single (r₁ v) 1)))
      ∧ (∀ v, Divisor.degree
            (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
              (Finsupp.single v 1))
          = Divisor.degree
            (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
              (Finsupp.single (r₁ v) 1)))

      ∧ (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
          (rℓ W).restrictAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
            = r₁ (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ))
      ∧ (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
          (rℓ W).restrictAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
            = r₁ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (N * ℓ) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero⟩
  haveI : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsAlgClosed (ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hqNl : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact hqN h1
    · exact hℓq (((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h2).symm)

  have hmain :=
    ModularCurve.exists_charLDegeneracyRoof_regularProlongation_heckeCompat_of_ne_of_residue_jq_jqN
      N q hq hqN A hA ℓ hℓq hαℓ hβℓ hαc hβc hdeg1 R₁ r₁ hr₁ hj hjN
  obtain ⟨Rℓ, rℓ, hrℓ, hRα, hRβ, hdegα, hdegβ⟩ := hmain
  refine ⟨Rℓ, rℓ, hrℓ, hRα, hRβ, hdegα, hdegβ, ?_⟩

  haveI : IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N
  have hdegF : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar N
  have hdegF' : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), W.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar (N * ℓ)
  have hdegFb : ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
      Q.deg = 1 := fun Q => IsCurveOver.deg_eq_one_of_isAlgClosed Q
  have hdiv : ∀ m : ℤ, m ≠ 0 →
      Function.Surjective fun x : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N) => m • x :=
    fun m hm => jZero_zsmul_surjective N m hm
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  constructor
  ·
    have hFI₀ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ :=
      fundamentalIdentityAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
        (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N ℓ)
        (separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ)
    have hFIq : FundamentalIdentityAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ)
        hαc :=
      fundamentalIdentityAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
        (finiteAlong_heckeAlphaC (ResidueField ↥A) N ℓ)
        (separableAlong_heckeAlphaC_heckeBetaC (ResidueField ↥A) N ℓ hqNl).1
    intro W
    have hdown : ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Divisor.degree (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
          (Finsupp.single Q 1))
          = finrankAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ) := fun Q => by
      rw [Divisor.degree_pullbackAlong _ hαc hFIq, Divisor.degree_single, hdegFb, Nat.cast_one,
        mul_one, mul_one]
    have hup' : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.degree (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
          (Finsupp.single v 1))
          = finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) :=
      fun v => by
      rw [Divisor.degree_pullbackAlong _ hαℓ hFI₀, Divisor.degree_single, hdegF, Nat.cast_one,
        mul_one, mul_one]
    have hnn : (finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) : ℤ)
        = finrankAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ) := by
      have h := hdegα (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ)
      rw [hup', hdown] at h
      exact h
    have hup : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.degree (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ
          (Finsupp.single v 1))
          = finrankAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ) :=
      fun v => (hup' v).trans hnn
    have hn : 0 < finrankAlong (ResidueField ↥A) (heckeAlphaC (ResidueField ↥A) N ℓ) := by
      letI := algebraAlong (heckeAlphaC (ResidueField ↥A) N ℓ)
      haveI : Module.Finite (modularFunctionFieldC (ResidueField ↥A) N)
          (charLDegeneracyRoof (ResidueField ↥A) N ℓ) :=
        finiteAlong_heckeAlphaC (ResidueField ↥A) N ℓ
      exact Module.finrank_pos
    exact PlaceCompat.restrictAlong_placeMap_eq_placeMap_restrictAlong
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ (heckeAlphaC (ResidueField ↥A) N ℓ) hαc
      R₁ Rℓ r₁ rℓ hr₁ hrℓ hRα hdegF hdegF' hdegFb hdeg1 hdiv _ hn hup hdown W
  ·
    have hFI₀ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ :=
      fundamentalIdentityAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
        (finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N ℓ)
        (separableAlong_of_charZero (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ)
    have hFIq : FundamentalIdentityAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ)
        hβc :=
      fundamentalIdentityAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
        (finiteAlong_heckeBetaC (ResidueField ↥A) N ℓ)
        (separableAlong_heckeAlphaC_heckeBetaC (ResidueField ↥A) N ℓ hqNl).2
    intro W
    have hdown : ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Divisor.degree (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N ℓ) hβc
          (Finsupp.single Q 1))
          = finrankAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) := fun Q => by
      rw [Divisor.degree_pullbackAlong _ hβc hFIq, Divisor.degree_single, hdegFb, Nat.cast_one,
        mul_one, mul_one]
    have hup' : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.degree (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
          (Finsupp.single v 1))
          = finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) :=
      fun v => by
      rw [Divisor.degree_pullbackAlong _ hβℓ hFI₀, Divisor.degree_single, hdegF, Nat.cast_one,
        mul_one, mul_one]
    have hnn : (finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) : ℤ)
        = finrankAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) := by
      have h := hdegβ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ)
      rw [hup', hdown] at h
      exact h
    have hup : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.degree (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ
          (Finsupp.single v 1))
          = finrankAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) :=
      fun v => (hup' v).trans hnn
    have hn : 0 < finrankAlong (ResidueField ↥A) (heckeBetaC (ResidueField ↥A) N ℓ) := by
      letI := algebraAlong (heckeBetaC (ResidueField ↥A) N ℓ)
      haveI : Module.Finite (modularFunctionFieldC (ResidueField ↥A) N)
          (charLDegeneracyRoof (ResidueField ↥A) N ℓ) :=
        finiteAlong_heckeBetaC (ResidueField ↥A) N ℓ
      exact Module.finrank_pos
    exact PlaceCompat.restrictAlong_placeMap_eq_placeMap_restrictAlong
      (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ (heckeBetaC (ResidueField ↥A) N ℓ) hβc
      R₁ Rℓ r₁ rℓ hr₁ hrℓ hRβ hdegF hdegF' hdegFb hdeg1 hdiv _ hn hup hdown W

end S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne
end P2MW
export P2MW.S_ModularCurve_exists_charLDegeneracyRoof_regularProlongation_heckeCompat_restrictAlong_eq_of_ne (solution)
