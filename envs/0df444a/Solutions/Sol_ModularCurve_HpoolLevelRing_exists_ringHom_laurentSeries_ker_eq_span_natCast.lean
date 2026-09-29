-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_ringHom_laurentSeries_ker_eq_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e3a29cf5-3b0b-583f-8b84-718f49844806

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_ringHom_laurentSeries_ker_eq_span_natCast
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing ModularCurve.IgusaScheme
open scoped TensorProduct

namespace LevelL

section Generic

variable {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [Algebra R K]
  {C : Type*} [CommRing C] [Algebra R C]

theorem mem_maximalIdeal_smul_of_one_tmul_eq_zero
    (hker : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R K r = 0)
    (c : C) (hc : (1 : K) ⊗ₜ[R] c = 0) :
    c ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C) := by
  classical

  let k₀ := IsLocalRing.ResidueField R
  let θ : k₀ →+* K := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R K) hker
  letI : Algebra k₀ K := θ.toAlgebra
  haveI : IsScalarTower R k₀ K := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R K r = θ (Ideal.Quotient.mk _ r)
    exact (Ideal.Quotient.lift_mk _ _ _).symm)

  let e := (Algebra.TensorProduct.cancelBaseChange R k₀ k₀ K C).symm
  have h1 : e ((1 : K) ⊗ₜ[R] c) = (1 : K) ⊗ₜ[k₀] ((1 : k₀) ⊗ₜ[R] c) := by
    simp [e, Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  have h2 : (1 : K) ⊗ₜ[k₀] ((1 : k₀) ⊗ₜ[R] c) = 0 := by rw [← h1, hc, map_zero]

  have h3 : ((1 : k₀) ⊗ₜ[R] c) = 0 := by
    have hinj := Algebra.TensorProduct.includeRight_injective (R := k₀) (A := K) (B := k₀ ⊗[R] C)
      (algebraMap k₀ K).injective
    apply hinj
    simpa [Algebra.TensorProduct.includeRight_apply] using h2

  have h4 : (TensorProduct.quotTensorEquivQuotSMul C (IsLocalRing.maximalIdeal R)) ((1 : k₀) ⊗ₜ[R] c) =
      Submodule.Quotient.mk c := by
    change (TensorProduct.quotTensorEquivQuotSMul C (IsLocalRing.maximalIdeal R))
      ((Ideal.Quotient.mk _ 1) ⊗ₜ[R] c) = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h5 := congrArg (TensorProduct.quotTensorEquivQuotSMul C (IsLocalRing.maximalIdeal R)) h3
  have h5' : (TensorProduct.quotTensorEquivQuotSMul C (IsLocalRing.maximalIdeal R)) 0 = 0 :=
    LinearEquiv.map_zero _
  have h6 : Submodule.Quotient.mk (p := (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) c = 0 :=
    h4.symm.trans (h5.trans h5')
  exact (Submodule.Quotient.mk_eq_zero _).1 h6

end Generic

variable (p : ℕ) [Fact p.Prime] [NeZero p]

noncomputable abbrev jA : Afin p :=
  AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

set_option maxHeartbeats 6400000 in

theorem exists_fibreMap (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ∃ (K : Type) (_ : Field K) (_ : CharP K q) (_ : IsAlgClosed K) (φ : Afin p →+* LaurentSeries K),
      RingHom.ker φ = Ideal.span {(q : Afin p)} ∧ φ (jA p) = jqModC K := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, hq⟩
  haveI hchar : CharP (IsLocalRing.ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime q A hA
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime q A hA
  letI algK : Algebra ↥(GaloisRep.ratLocalizedAt q) (IsLocalRing.ResidueField ↥A) :=
    ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  have hqN : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).1 h)
  obtain ⟨⟨eFin, heFin⟩, -⟩ :=
    IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing p q hqN A hA ρ hρ

  let K := IsLocalRing.ResidueField ↥A
  let Zq := ↥(GaloisRep.ratLocalizedAt q)
  let F := ↥(modularFunctionFieldFull p)
  let C := ↥(IgusaScheme.chartAlgFin p q)
  haveI : IsLocalRing Zq := GaloisRep.ratLocalizedAt.isLocalRing hq

  have hKq : algebraMap Zq K (q : Zq) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero K q
  have hker : ∀ r ∈ IsLocalRing.maximalIdeal Zq, algebraMap Zq K r = 0 := by
    intro r hr
    rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hq, Ideal.mem_span_singleton'] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [map_mul, hKq, mul_zero]

  have hmem : ∀ x : Afin p, (x : F) ∈ IgusaScheme.chartAlgFin p q := by
    intro x
    rw [IgusaScheme.mem_chartAlg_iff]
    have hx : IsIntegral (Algebra.adjoin ℤ {IgusaScheme.jFull p}) (x : F) :=
      (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ℤ F).1 x.2
    have hle : Algebra.adjoin ℤ {IgusaScheme.jFull p} ≤
        (Algebra.adjoin Zq {IgusaScheme.jFull p}).restrictScalars ℤ :=
      Algebra.adjoin_le (by rw [Subalgebra.coe_restrictScalars]; exact Algebra.subset_adjoin)
    let f : ↥(Algebra.adjoin ℤ {IgusaScheme.jFull p}) →+* ↥(Algebra.adjoin Zq {IgusaScheme.jFull p}) :=
      { toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact hx.map_of_comp_eq f (RingHom.id F) (by ext; rfl)
  let ι : Afin p →+* C :=
    { toFun := fun x => ⟨x.1, hmem x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ x : Afin p, ((ι x : C) : F) = (x : F) := fun _ => rfl

  let B := ↥(AlgebraicCurve.CurveModel.chartRing K
    ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p)))
  let out1 : B →+* ↥(modularFunctionFieldFullC K p) := (Subalgebra.val _).toRingHom
  let out2 : ↥(modularFunctionFieldFullC K p) →+* LaurentSeries K :=
    { toFun := fun z => (z : LaurentSeries K), map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hout : Function.Injective (out2.comp out1) :=
    Subtype.val_injective.comp Subtype.val_injective
  let inC : C →+* K ⊗[Zq] C := (Algebra.TensorProduct.includeRight (R := Zq) (A := K) (B := C)).toRingHom
  have hinC : ∀ c : C, inC c = (1 : K) ⊗ₜ[Zq] c := fun _ => rfl
  let φ : Afin p →+* LaurentSeries K :=
    (out2.comp out1).comp (eFin.toAlgHom.toRingHom.comp (inC.comp ι))
  refine ⟨K, inferInstance, hchar, inferInstance, φ, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx

      have h1 : eFin (inC (ι x)) = 0 := hout (by
        rw [map_zero]; exact hx)
      have h2 : (1 : K) ⊗ₜ[Zq] (ι x) = 0 := by
        rw [← hinC]; exact eFin.injective (by rw [map_zero]; exact h1)

      have h3 := mem_maximalIdeal_smul_of_one_tmul_eq_zero hker (ι x) h2
      rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hq,
        Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
      obtain ⟨c', -, hc'⟩ := h3
      have hxF : (x : F) = (q : F) * (c' : F) := by
        have := congrArg (fun z : C => (z : F)) hc'
        try simp only at this
        rw [hι] at this
        rw [← this, Subalgebra.coe_smul, Algebra.smul_def, map_natCast]

      haveI hprime : (Ideal.span {(q : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq)
      haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
      obtain ⟨e0, he0⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg ℤ Zq F
        ((Ideal.span {(q : ℤ)}).primeCompl) ({IgusaScheme.jFull p} : Set F)
      have hden : ∀ z : Zq ⊗[ℤ] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg ℤ F {IgusaScheme.jFull p}),
          ∃ s : ℤ, s ∈ (Ideal.span {(q : ℤ)}).primeCompl ∧
            ∃ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg ℤ F {IgusaScheme.jFull p}),
              (s : F) * (e0 z : F) = (a : F) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => exact ⟨1, Submonoid.one_mem _, 0, by simp⟩
        | tmul r b =>
          obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj ((Ideal.span {(q : ℤ)}).primeCompl) r
          dsimp only at hs
          refine ⟨s, s.2, a • b, ?_⟩
          have h1 : ((s : ℤ) : F) * algebraMap Zq F r = algebraMap Zq F (r * algebraMap ℤ Zq s) := by
            rw [map_mul, ← IsScalarTower.algebraMap_apply ℤ Zq F, eq_intCast, mul_comm]
          rw [he0, Algebra.smul_def, ← mul_assoc, h1, hs, ← IsScalarTower.algebraMap_apply ℤ Zq F,
            eq_intCast, Subalgebra.coe_smul, zsmul_eq_mul]
        | add z w hz hw =>
          obtain ⟨s₁, hs₁, a₁, h₁⟩ := hz
          obtain ⟨s₂, hs₂, a₂, h₂⟩ := hw
          refine ⟨s₁ * s₂, Submonoid.mul_mem _ hs₁ hs₂, s₂ • a₁ + s₁ • a₂, ?_⟩
          rw [map_add, Subalgebra.coe_add, mul_add, Subalgebra.coe_add, Subalgebra.coe_smul,
            Subalgebra.coe_smul, zsmul_eq_mul, zsmul_eq_mul, ← h₁, ← h₂]
          push_cast
          ring

      let c'' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg Zq F {IgusaScheme.jFull p}) :=
        ⟨(c' : F), (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff Zq F).2
          ((IgusaScheme.mem_chartAlg_iff p q).1 c'.2)⟩
      obtain ⟨s, hs, a, ha⟩ := hden (e0.symm c'')
      rw [AlgEquiv.apply_symm_apply] at ha
      change (s : F) * (c' : F) = (a : F) at ha

      have hsq : ¬ (q : ℤ) ∣ s := fun h => hs (Ideal.mem_span_singleton.2 h)
      have hcop : IsCoprime (s : ℤ) q :=
        ((Nat.prime_iff_prime_int.1 hq).coprime_iff_not_dvd.2 hsq).symm
      obtain ⟨u, v, huv⟩ := hcop

      refine Ideal.mem_span_singleton'.2 ⟨⟨u * (a : F) + v * (x : F), ?_⟩, ?_⟩
      · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ u) a.2)
          (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ v) x.2)
      · apply Subtype.ext
        change (u * (a : F) + v * (x : F)) * (q : F) = (x : F)
        have h1F : (x : F) = ((u * s + v * q : ℤ) : F) * (x : F) := by rw [huv]; push_cast; ring
        rw [← ha]
        nth_rewrite 2 [h1F]
        rw [hxF]
        push_cast
        ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      have hq0 : (inC.comp ι) (q : Afin p) = 0 := by
        rw [map_natCast, ← map_natCast (algebraMap Zq (K ⊗[Zq] C)) q,
          Algebra.TensorProduct.algebraMap_apply, hKq, TensorProduct.zero_tmul]
      change (out2.comp out1) (eFin ((inC.comp ι) (q : Afin p))) = 0
      rw [hq0, map_zero, map_zero]
  ·
    have hj : ι (jA p) = IgusaScheme.jChartFin p q := Subtype.ext rfl
    change ((eFin (inC (ι (jA p)))).1 : LaurentSeries K) = jqModC K
    rw [hj, hinC, heFin]

end LevelL

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ∃ (K : Type) (_ : Field K) (_ : CharP K q) (_ : IsAlgClosed K)
      (φ : ModularCurve.HpoolLevelRing.Afin p →+* LaurentSeries K),
      RingHom.ker φ = Ideal.span {(q : ModularCurve.HpoolLevelRing.Afin p)} ∧
      φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(ModularCurve.modularFunctionFieldFull p)
          (ModularCurve.IgusaScheme.jFull p)) = ModularCurve.jqModC K :=
  LevelL.exists_fibreMap p q hq hqp

end S_ModularCurve_HpoolLevelRing_exists_ringHom_laurentSeries_ker_eq_span_natCast
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_ringHom_laurentSeries_ker_eq_span_natCast (solution)
