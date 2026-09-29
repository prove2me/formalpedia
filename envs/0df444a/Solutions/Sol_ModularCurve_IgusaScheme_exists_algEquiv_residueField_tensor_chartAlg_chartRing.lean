-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3dadfee4-3b3b-5afc-aed2-441f35a88034

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
import Theorems.Thm_ModularCurve_IgusaScheme_exists_fibreModel_cuspChart_of_chartAlg
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_IgusaScheme_chartRing_le_span_coeffEmb_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
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
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve"

noncomputable section

namespace FibreIsoAux

theorem mem_of_isIntegral_of_mul_mem {T : Type*} [Field T] (R : Subring T) [IsIntegrallyClosed R]
    (x : T) (r₁ r₂ : R) (hr₁ : r₁ ≠ 0) (hx : (r₁ : T) * x = r₂) (hint : IsIntegral R x) : x ∈ R := by
  classical
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R T) := Subtype.val_injective
  let lift : K →+* T := IsFractionRing.lift hinj
  have hlift : ∀ r : R, lift (algebraMap R K r) = (r : T) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hliftinj : Function.Injective lift := lift.injective

  let z : K := algebraMap R K r₂ / algebraMap R K r₁
  have hr₁K : algebraMap R K r₁ ≠ 0 :=
    fun h => hr₁ ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  have hz : lift z = x := by
    have hr₁T : (r₁ : T) ≠ 0 := fun h => hr₁ (Subtype.ext h)
    rw [map_div₀, hlift, hlift]
    field_simp
    rw [← hx, mul_comm]

  have hzint : IsIntegral R z := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p, hp, ?_⟩
    apply hliftinj
    rw [Polynomial.hom_eval₂, hz, map_zero]
    have : lift.comp (algebraMap R K) = algebraMap R T := RingHom.ext hlift
    rw [this]
    exact hpx
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
  have : (r : T) = x := by rw [← hlift r, hr, hz]
  rw [← this]
  exact r.2

end FibreIsoAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull modularFunctionFieldFullC jqModC_mem_full jqModC modularFunctionFieldC jqModC_mem coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange CharPModel.jBar IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed IgusaScheme.exists_fibreModel_cuspChart_of_chartAlg modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField IgusaScheme.chartRing_le_span_coeffEmb_chartAlg"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull chartAlgFin chartAlgInf jChartFin jInvChartInf exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed exists_fibreModel_cuspChart_of_chartAlg chartRing_le_span_coeffEmb_chartAlg"
namespace FibreIsoK
p2m_open "ModularCurve.IgusaScheme ModularCurve~jBar"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "TT" => ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
set_option quotPrecheck false in
local notation "kA" => ResidueField ↥A

section Generic

variable (S : Subalgebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N))

def AS : Type := ↥A ⊗[ℤℓ] S

scoped instance : CommRing (AS N ℓ A S) := Algebra.TensorProduct.instCommRing
scoped instance : Algebra ↥A (AS N ℓ A S) := Algebra.TensorProduct.leftAlgebra

def asEquiv : (↥A ⊗[ℤℓ] S) ≃ₐ[↥A] AS N ℓ A S := AlgEquiv.refl

def e3 : kA ⊗[ℤℓ] S ≃ₐ[↥A] (AS N ℓ A S) ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS N ℓ A S)) :=
  Algebra.TensorProduct.quotientTensorEquiv (R := ℤℓ) ↥A S ↥A (maximalIdeal ↥A)

theorem e3_tmul (a : ↥A) (b : S) :
    e3 N ℓ A S (residue ↥A a ⊗ₜ b) = Ideal.Quotient.mk _ (asEquiv N ℓ A S (a ⊗ₜ b)) :=
  Algebra.TensorProduct.quotientTensorEquiv_apply_tmul (R := ℤℓ) ↥A S ↥A (maximalIdeal ↥A) a b

variable [Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))]

theorem b2 (L : Type) [Field L]
    (ψ : AS N ℓ A S →ₐ[↥A] TT) (hinj : Function.Injective ψ)
    (B : Subring TT) (hψB : ∀ t, ψ t ∈ B) (hBψ : ∀ x ∈ B, ∃ t, ψ t = x)
    (π : ↥B →+* L)
    (hker : RingHom.ker π =
      Ideal.span ((fun a : ↥A => (⟨ψ (algebraMap ↥A _ a), hψB _⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A))) :
    ∃ Pr : AS N ℓ A S →+* L, (∀ t, Pr t = π ⟨ψ t, hψB t⟩) ∧ Pr.range = π.range ∧
      RingHom.ker Pr = (maximalIdeal ↥A).map (algebraMap ↥A (AS N ℓ A S)) := by
  classical

  let ψB : AS N ℓ A S →+* ↥B := (ψ.toRingHom).codRestrict B hψB
  have hbij : Function.Bijective ψB :=
    ⟨fun x y h => hinj (congrArg Subtype.val h), fun x => by
      obtain ⟨t, ht⟩ := hBψ x x.2
      exact ⟨t, Subtype.ext ht⟩⟩
  let ρψ : AS N ℓ A S ≃+* ↥B := RingEquiv.ofBijective ψB hbij
  have hρψ : ∀ t, (ρψ t : TT) = ψ t := fun t => rfl
  let Pr : AS N ℓ A S →+* L := π.comp ρψ.toRingHom
  refine ⟨Pr, fun t => rfl, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨ρψ t, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨ρψ.symm x, ?_⟩
      change π (ρψ (ρψ.symm x)) = π x
      rw [RingEquiv.apply_symm_apply]
  · have h1 : RingHom.ker Pr = (RingHom.ker π).comap ρψ := by
      ext t
      rfl
    rw [h1, hker, ← Ideal.map_symm, Ideal.map_span]
    have himg : (ρψ.symm : ↥B → AS N ℓ A S) ''
        ((fun a : ↥A => (⟨ψ (algebraMap ↥A _ a), hψB _⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) =
        (algebraMap ↥A (AS N ℓ A S)) '' (maximalIdeal ↥A : Set ↥A) := by
      rw [Set.image_image]
      refine Set.image_congr fun a _ => ?_
      change ρψ.symm _ = algebraMap ↥A (AS N ℓ A S) a
      apply ρψ.injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [himg]
    rfl

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in

theorem exists_denom (s : Finset Qb) : ∃ d : ↥A, d ≠ 0 ∧ ∀ q ∈ s, (d : Qb) * q ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun q hq => absurd hq (by simp)⟩
  | insert q s hqs ih =>
    obtain ⟨d, hd0, hd⟩ := ih
    rcases A.mem_or_inv_mem q with hq | hq
    · refine ⟨d, hd0, fun r hr => ?_⟩
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact A.mul_mem _ _ d.2 hq
      · exact hd r hr
    · by_cases hq0 : q = 0
      · refine ⟨d, hd0, fun r hr => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · rw [hq0, mul_zero]; exact A.zero_mem
        · exact hd r hr
      · refine ⟨⟨(d : Qb) * q⁻¹, A.mul_mem _ _ d.2 hq⟩, ?_, fun r hr => ?_⟩
        · intro h
          have h' : (d : Qb) * q⁻¹ = 0 := congrArg Subtype.val h
          rcases mul_eq_zero.mp h' with h1 | h1
          · exact hd0 (Subtype.ext h1)
          · exact hq0 (inv_eq_zero.mp h1)
        · rcases Finset.mem_insert.mp hr with rfl | hr
          · change (d : Qb) * r⁻¹ * r ∈ A
            rw [inv_mul_cancel_right₀ hq0]
            exact d.2
          · change (d : Qb) * q⁻¹ * r ∈ A
            rw [mul_assoc, mul_comm q⁻¹, ← mul_assoc]
            exact A.mul_mem _ _ (hd r hr) hq

def embS (b : S) : TT :=
  ⟨coeffEmb Qb ((b : FN) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (b : FN).2⟩

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
@[scoped simp] theorem coe_embS (b : S) :
    (embS N ℓ S b : LaurentSeries Qb) = coeffEmb Qb ((b : FN) : LaurentSeries ℚ) := rfl

theorem b1 (ψ : AS N ℓ A S →ₐ[↥A] TT) (hIC : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv N ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS N ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom N A a)
    (g : TT)
    (base : Subring TT) (hbase : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hbase' : ∀ x ∈ base, ∃ t, ψ t = x)
    (B : Subring TT)
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (hSB : ∀ b : S, embS N ℓ S b ∈ B) (hconstB : ∀ a : ↥A, constantsHom N A a ∈ B)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS N ℓ S))) :
    ∀ x : TT, x ∈ B ↔ ∃ t, ψ t = x := by
  classical
  have hconst : ∀ a : ↥A, algebraMap ↥A TT a = algebraMap Qb TT (a : Qb) := fun a => by
    rw [hcT]; rfl
  intro x
  constructor
  · intro hxB

    obtain ⟨p, hp, hpx⟩ := hBint ⟨x, hxB⟩
    let incl : ↥base →+* ↥(Algebra.adjoin Qb ({g} : Set TT)) :=
      { toFun := fun y => ⟨y, hbase y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hint : IsIntegral (Algebra.adjoin Qb ({g} : Set TT)) x := by
      refine ⟨p.map incl, hp.map incl, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxchart : x ∈ CurveModel.chartRing Qb ({g} : Set TT) := hint

    have hxspan : x ∈ Submodule.span Qb (Set.range (embS N ℓ S)) := hspan hxchart
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hxspan

    obtain ⟨d, hd0, hd⟩ := exists_denom A (c.support.image c)
    have hdc : ∀ b ∈ c.support, (d : Qb) * c b ∈ A := fun b hb => hd _ (Finset.mem_image_of_mem c hb)

    have hy : ∃ t, ψ t = algebraMap ↥A TT d * x := by
      refine ⟨asEquiv N ℓ A S (∑ b ∈ c.support.attach,
        (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S)), ?_⟩
      have e1 : ψ (asEquiv N ℓ A S (∑ b ∈ c.support.attach,
          (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S))) =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS N ℓ S b.1) := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hψ, Algebra.smul_def, ← mul_assoc, hconst, hconst]
        congr 1
        change algebraMap Qb TT ((d : Qb) * c b.1) = _
        rw [map_mul]
      have e2 : algebraMap ↥A TT d * x =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS N ℓ S b.1) := by
        rw [← hc, Finsupp.sum, Finset.mul_sum]
        exact (Finset.sum_attach c.support (fun b => algebraMap ↥A TT d * (c b • embS N ℓ S b))).symm
      exact e1.trans e2.symm

    let R : Subring TT := ψ.range.toSubring
    haveI : IsIntegrallyClosed ↥R := hIC
    have hd_mem : algebraMap ↥A TT d ∈ R := ⟨algebraMap ↥A _ d, ψ.commutes d⟩
    obtain ⟨t, ht⟩ := hy
    have hy_mem : algebraMap ↥A TT d * x ∈ R := ⟨t, ht⟩
    have hr₁ : (⟨algebraMap ↥A TT d, hd_mem⟩ : ↥R) ≠ 0 := by
      intro h
      have h' : algebraMap ↥A TT d = 0 := congrArg Subtype.val h
      rw [hconst] at h'
      exact hd0 (Subtype.ext ((algebraMap Qb TT).injective (h'.trans (map_zero _).symm)))
    let incl' : ↥base →+* ↥R :=
      { toFun := fun y => ⟨y, by obtain ⟨t, ht⟩ := hbase' y y.2; exact ⟨t, ht⟩⟩,
        map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hintR : IsIntegral ↥R x := by
      refine ⟨p.map incl', hp.map incl', ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxR : x ∈ R := FibreIsoAux.mem_of_isIntegral_of_mul_mem R x ⟨algebraMap ↥A TT d, hd_mem⟩
      ⟨algebraMap ↥A TT d * x, hy_mem⟩ hr₁ rfl hintR
    exact hxR
  · rintro ⟨t, rfl⟩
    change ψ t ∈ B
    induction t using TensorProduct.induction_on with
    | zero =>
      convert B.zero_mem
      exact map_zero ψ
    | tmul a b =>
      have := hψ a b
      change ψ (a ⊗ₜ b) = _ at this
      rw [this, hcT]
      exact B.mul_mem (hconstB a) (hSB b)
    | add x y hx hy =>
      convert B.add_mem hx hy using 1
      exact map_add ψ x y

theorem b4 (B base : Subring TT) (hbaseB : base ≤ B) (g : TT)
    (hbase_le : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {g}))
    (hgen : Set.range (constantsHom N A) ∪ {g} ⊆ (base : Set TT))
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (Lk : Type) [Field Lk] [Algebra kA Lk] (π : ↥B →+* Lk) (h : Lk)
    (hgB : g ∈ B) (hπg : π ⟨g, hgB⟩ = h)
    (hcB : ∀ a : ↥A, constantsHom N A a ∈ B)
    (hπc : ∀ a : ↥A, π ⟨constantsHom N A a, hcB a⟩ = algebraMap kA Lk (residue ↥A a))
    (hIC : ∀ y : Lk, (∃ p : Polynomial ↥π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype y p = 0) →
      y ∈ π.range) :
    ∀ y : Lk, y ∈ π.range ↔ IsIntegral (Algebra.adjoin kA ({h} : Set Lk)) y := by
  classical
  set R₀ := Algebra.adjoin kA ({h} : Set Lk) with hR₀
  have hsB : ∀ y ∈ Subring.closure (Set.range (constantsHom N A) ∪ {g}), y ∈ B :=
    fun y hy => hbaseB (Subring.closure_le.mpr hgen hy)

  have hland : ∀ (y : TT) (hy : y ∈ Subring.closure (Set.range (constantsHom N A) ∪ {g}))
      (hyB : y ∈ B), π ⟨y, hyB⟩ ∈ R₀ := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      intro hyB
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [show π ⟨constantsHom N A a, hyB⟩ = π ⟨constantsHom N A a, hcB a⟩ from rfl, hπc]
        exact Subalgebra.algebraMap_mem _ _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [show π ⟨y, hyB⟩ = π ⟨y, hgB⟩ from rfl, hπg]
        exact Algebra.subset_adjoin rfl
    | zero => intro hyB; rw [show (⟨0, hyB⟩ : ↥B) = 0 from rfl, map_zero]; exact zero_mem _
    | one => intro hyB; rw [show (⟨1, hyB⟩ : ↥B) = 1 from rfl, map_one]; exact one_mem _
    | add x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x + z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ + ⟨z, hsB z hz⟩ from rfl, map_add]
      exact add_mem (ihx _) (ihz _)
    | neg x hx ihx =>
      intro hB
      rw [show (⟨-x, hB⟩ : ↥B) = -⟨x, hsB x hx⟩ from rfl, map_neg]
      exact neg_mem (ihx _)
    | mul x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x * z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ * ⟨z, hsB z hz⟩ from rfl, map_mul]
      exact mul_mem (ihx _) (ihz _)

  let inclB : ↥base →+* ↥B :=
    { toFun := fun x => ⟨x, hbaseB x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ : ↥base →+* ↥R₀ :=
    (π.comp inclB).codRestrict R₀ (fun x => hland x (hbase_le x.2) (hbaseB x.2))
  intro y
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨p, hp, hpb⟩ := hBint b
    have hrelB : Polynomial.eval₂ inclB b p = 0 := by
      apply Subtype.val_injective
      change B.subtype (Polynomial.eval₂ inclB b p) = ((0 : ↥B) : TT)
      rw [Polynomial.hom_eval₂]
      exact hpb
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥R₀ Lk).comp φ = π.comp inclB := RingHom.ext fun _ => rfl
    rw [hcomp, ← Polynomial.hom_eval₂, hrelB, map_zero]
  · intro hy

    have hconst : ∀ x : kA, algebraMap kA Lk x ∈ π.range := by
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨⟨constantsHom N A a, hcB a⟩, hπc a⟩
    let πS : Subalgebra kA Lk :=
      { π.range with algebraMap_mem' := hconst }
    have hle : R₀ ≤ πS := Algebra.adjoin_le (by rintro _ rfl; exact ⟨⟨g, hgB⟩, hπg⟩)
    let ι : ↥R₀ →+* ↥π.range :=
      { toFun := fun x => ⟨x, hle x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨p, hp, hpy⟩ := hy
    refine hIC y ⟨p.map ι, hp.map ι, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : π.range.subtype.comp ι = algebraMap ↥R₀ Lk := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hpy

theorem isIntegral_adjoin_singleton_iff_of_algEquiv {L₁ L₂ : Type} [Field L₁] [Field L₂]
    [Algebra kA L₁] [Algebra kA L₂] (e : L₁ ≃ₐ[kA] L₂) (s : L₁) (x : L₂) :
    IsIntegral (Algebra.adjoin kA ({e s} : Set L₂)) x ↔
      IsIntegral (Algebra.adjoin kA ({s} : Set L₁)) (e.symm x) := by

  have hmap : ∀ z : L₁, z ∈ Algebra.adjoin kA ({s} : Set L₁) → e z ∈ Algebra.adjoin kA ({e s} : Set L₂) := by
    intro z hz
    have : Algebra.adjoin kA ({e s} : Set L₂) = (Algebra.adjoin kA ({s} : Set L₁)).map e.toAlgHom := by
      rw [AlgHom.map_adjoin]
      simp
    rw [this]
    exact ⟨z, hz, rfl⟩
  have hmap' : ∀ z : L₂, z ∈ Algebra.adjoin kA ({e s} : Set L₂) → e.symm z ∈ Algebra.adjoin kA ({s} : Set L₁) := by
    intro z hz
    have : Algebra.adjoin kA ({s} : Set L₁) = (Algebra.adjoin kA ({e s} : Set L₂)).map e.symm.toAlgHom := by
      rw [AlgHom.map_adjoin]
      simp
    rw [this]
    exact ⟨z, hz, rfl⟩
  let φ : ↥(Algebra.adjoin kA ({s} : Set L₁)) →+* ↥(Algebra.adjoin kA ({e s} : Set L₂)) :=
    (e.toAlgHom.toRingHom.comp (Algebra.adjoin kA ({s} : Set L₁)).val.toRingHom).codRestrict _
      (fun z => hmap z z.2)
  let φ' : ↥(Algebra.adjoin kA ({e s} : Set L₂)) →+* ↥(Algebra.adjoin kA ({s} : Set L₁)) :=
    (e.symm.toAlgHom.toRingHom.comp (Algebra.adjoin kA ({e s} : Set L₂)).val.toRingHom).codRestrict _
      (fun z => hmap' z z.2)
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map φ', hp.map φ', ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(Algebra.adjoin kA ({s} : Set L₁)) L₁).comp φ' =
        e.symm.toAlgHom.toRingHom.comp (algebraMap ↥(Algebra.adjoin kA ({e s} : Set L₂)) L₂) :=
      RingHom.ext fun _ => rfl
    rw [hcomp, show e.symm x = e.symm.toAlgHom.toRingHom x from rfl, ← Polynomial.hom_eval₂, hpx, map_zero]
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(Algebra.adjoin kA ({e s} : Set L₂)) L₂).comp φ =
        e.toAlgHom.toRingHom.comp (algebraMap ↥(Algebra.adjoin kA ({s} : Set L₁)) L₁) :=
      RingHom.ext fun _ => rfl
    rw [hcomp, show x = e.toAlgHom.toRingHom (e.symm x) from (e.apply_symm_apply x).symm,
      ← Polynomial.hom_eval₂, hpx, map_zero]

set_option maxHeartbeats 32000000 in

theorem assemble
    (ψ : AS N ℓ A S →ₐ[↥A] TT) (hinj : Function.Injective ψ) (hICψ : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv N ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS N ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom N A a)
    (B base : Subring TT) (hbaseB : base ≤ B) (g : TT) (b₀ : S) (hb₀ : embS N ℓ S b₀ = g)
    (hbase_le : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {g}))
    (hgen : Set.range (constantsHom N A) ∪ {g} ⊆ (base : Set TT))
    (hbase_adj : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (hSB : ∀ b : S, embS N ℓ S b ∈ B) (hconstB : ∀ a : ↥A, constantsHom N A a ∈ B)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS N ℓ S)))
    (π : ↥B →+* ↥(modularFunctionFieldC kA N)) (h : ↥(modularFunctionFieldC kA N))
    (hgB : g ∈ B) (hπg : π ⟨g, hgB⟩ = h)
    (hπc : ∀ a : ↥A, π ⟨constantsHom N A a, hconstB a⟩ =
      algebraMap kA ↥(modularFunctionFieldC kA N) (residue ↥A a))
    (hker : RingHom.ker π =
      Ideal.span ((fun a : ↥A => (⟨constantsHom N A a, hconstB a⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)))
    (hICπ : ∀ y : ↥(modularFunctionFieldC kA N),
      (∃ p : Polynomial ↥π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype y p = 0) → y ∈ π.range)
    (hEq : modularFunctionFieldFullC kA N = modularFunctionFieldC kA N)
    (hF : ↥(modularFunctionFieldFullC kA N))
    (hhF : (IntermediateField.equivOfEq hEq).symm h = hF) :
    ∃ eq : kA ⊗[ℤℓ] S ≃ₐ[kA] ↥(CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N))),
      (eq ((1 : kA) ⊗ₜ[ℤℓ] b₀)).1 = hF := by
  classical

  letI iC : Algebra kA ↥(modularFunctionFieldC kA N) := inferInstance
  letI iF : Algebra kA ↥(modularFunctionFieldFullC kA N) := inferInstance
  letI iKS : Algebra kA (kA ⊗[ℤℓ] S) := inferInstance
  set e : ↥(modularFunctionFieldC kA N) ≃ₐ[kA] ↥(modularFunctionFieldFullC kA N) :=
    (IntermediateField.equivOfEq hEq).symm with he
  have hg : ∃ t, ψ t = g := ⟨asEquiv N ℓ A S ((1 : ↥A) ⊗ₜ b₀), by rw [hψ, map_one, one_mul, hb₀]⟩

  have hbase' : ∀ x ∈ base, ∃ t, ψ t = x := by
    intro x hx
    have hcl : Subring.closure (Set.range (constantsHom N A) ∪ {g}) ≤ ψ.range.toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact ⟨algebraMap ↥A _ a, by change ψ (algebraMap ↥A _ a) = _; rw [ψ.commutes, hcT]⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hg
    exact hcl (hbase_le hx)
  have hB : ∀ x : TT, x ∈ B ↔ ∃ t, ψ t = x :=
    b1 N ℓ A S ψ hICψ hψ hcT g base hbase_adj hbase' B hBint hSB hconstB hspan

  have hker' : RingHom.ker π = Ideal.span ((fun a : ↥A =>
      (⟨ψ (algebraMap ↥A _ a), (hB _).mpr ⟨_, rfl⟩⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) := by
    rw [hker]
    congr 2
    funext a
    apply Subtype.ext
    change constantsHom N A a = ψ (algebraMap ↥A _ a)
    rw [ψ.commutes, hcT]
  obtain ⟨Pr, hPr, hrange, hkerPr⟩ :=
    b2 N ℓ A S ↥(modularFunctionFieldC kA N) ψ hinj B (fun t => (hB _).mpr ⟨t, rfl⟩)
      (fun x hx => (hB x).mp hx) π hker'

  have hb4 : ∀ y : ↥(modularFunctionFieldC kA N),
      y ∈ π.range ↔ IsIntegral (Algebra.adjoin kA ({h} : Set ↥(modularFunctionFieldC kA N))) y :=
    b4 N A B base hbaseB g hbase_le hgen hBint ↥(modularFunctionFieldC kA N) π h hgB hπg hconstB hπc hICπ

  let E1 : kA ⊗[ℤℓ] S ≃+* AS N ℓ A S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS N ℓ A S)) :=
    (e3 N ℓ A S).toRingEquiv
  let E2 : (AS N ℓ A S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS N ℓ A S))) ≃+* ↥Pr.range :=
    (Ideal.quotEquivOfEq hkerPr.symm).trans (RingHom.quotientKerEquivRange Pr)
  have hE2 : ∀ t, (E2 (Ideal.Quotient.mk _ t) : ↥(modularFunctionFieldC kA N)) = Pr t := fun t => rfl
  let E3 : ↥Pr.range ≃+* ↥π.range := RingEquiv.subringCongr hrange
  have hmem : ∀ y : ↥(modularFunctionFieldC kA N), y ∈ π.range ↔
      e y ∈ CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N)) := by
    intro y
    rw [hb4, CurveModel.mem_chartRing_iff, ← hhF]
    exact ((isIntegral_adjoin_singleton_iff_of_algEquiv A e h (e y)).trans
      (by rw [AlgEquiv.symm_apply_apply])).symm
  let E4 : ↥π.range ≃+* ↥(CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N))) :=
    { toFun := fun y => ⟨e y.1, (hmem y.1).mp y.2⟩
      invFun := fun x => ⟨e.symm x.1, (hmem _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact x.2)⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  let E : kA ⊗[ℤℓ] S ≃+* ↥(CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N))) :=
    E1.trans (E2.trans (E3.trans E4))
  have hE : ∀ (a : ↥A) (b : S),
      ((E (residue ↥A a ⊗ₜ b)).1 : ↥(modularFunctionFieldFullC kA N)) =
        e (π ⟨ψ (asEquiv N ℓ A S (a ⊗ₜ b)), (hB _).mpr ⟨_, rfl⟩⟩) := by
    intro a b
    change e ((E3 (E2 (E1 (residue ↥A a ⊗ₜ b)))).1) = _
    congr 1
    change ((E2 (e3 N ℓ A S (residue ↥A a ⊗ₜ b)) : ↥Pr.range) : ↥(modularFunctionFieldC kA N)) = _
    rw [e3_tmul, hE2, hPr]

  have key : ∀ a : ↥A, E (algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a)) =
      algebraMap kA ↥(CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N))) (residue ↥A a) := by
    intro a
    apply Subtype.ext
    have h0 : algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a) = residue ↥A a ⊗ₜ (1 : S) := rfl
    have hL : ((E (algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a))).1 : ↥(modularFunctionFieldFullC kA N)) =
        (E (residue ↥A a ⊗ₜ (1 : S))).1 :=
      congrArg (fun t => ((E t).1 : ↥(modularFunctionFieldFullC kA N))) h0
    refine hL.trans ?_
    rw [hE]
    have h1 : ψ (asEquiv N ℓ A S (a ⊗ₜ (1 : S))) = constantsHom N A a := by
      rw [hψ, hcT]
      have : embS N ℓ S 1 = 1 := Subtype.ext (by simp [embS])
      rw [this, mul_one]
    have h2 : π ⟨ψ (asEquiv N ℓ A S (a ⊗ₜ (1 : S))), (hB _).mpr ⟨_, rfl⟩⟩ =
        algebraMap kA ↥(modularFunctionFieldC kA N) (residue ↥A a) := by
      rw [← hπc a]
      congr 1
      exact Subtype.ext h1
    rw [h2, AlgEquiv.commutes]
    rfl
  have hcomm : ∀ x : kA, E (algebraMap kA (kA ⊗[ℤℓ] S) x) =
      algebraMap kA ↥(CurveModel.chartRing kA ({hF} : Set ↥(modularFunctionFieldFullC kA N))) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact key a
  refine ⟨AlgEquiv.ofRingEquiv (f := E) hcomm, ?_⟩

  change ((E ((1 : kA) ⊗ₜ b₀)).1 : ↥(modularFunctionFieldFullC kA N)) = hF
  rw [show (1 : kA) = residue ↥A 1 from (map_one _).symm, hE, ← hhF]
  congr 1
  rw [← hπg]
  congr 1
  apply Subtype.ext
  change ψ (asEquiv N ℓ A S (1 ⊗ₜ b₀)) = g
  rw [hψ, map_one, one_mul, hb₀]

end Generic

end ModularCurve.IgusaScheme.FibreIsoK
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme.FibreIsoK"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve"

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve"
open ModularCurve.IgusaScheme.FibreIsoK

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    (∃ eFin : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A)
          ({⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩} :
            Set ↥(modularFunctionFieldFullC (ResidueField ↥A) N))),
      (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)).1 =
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
          ↥(modularFunctionFieldFullC (ResidueField ↥A) N))) ∧
    (∃ eInf : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A)
          ({(⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
              ↥(modularFunctionFieldFullC (ResidueField ↥A) N))⁻¹} :
            Set ↥(modularFunctionFieldFullC (ResidueField ↥A) N))),
      (eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)).1 =
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
          ↥(modularFunctionFieldFullC (ResidueField ↥A) N))⁻¹) := by
  classical
  letI i1 : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A := ρ.toAlgebra
  letI i2 : Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
    (constantsHom N A).toAlgebra

  obtain ⟨⟨ψF, hψF, hinjF, -, hICF⟩, ⟨ψI, hψI, hinjI, -, hICI⟩⟩ :=
    ModularCurve.IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed N ℓ hℓN A hA ρ hρ
  obtain ⟨fm, _, hmemF, hmemI⟩ :=
    ModularCurve.IgusaScheme.exists_fibreModel_cuspChart_of_chartAlg N ℓ hℓN A hA
  obtain ⟨hspanF, hspanI⟩ := ModularCurve.IgusaScheme.chartRing_le_span_coeffEmb_chartAlg N ℓ
  have hEq := ModularCurve.modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField N ℓ hℓN A hA
  have hcT : ∀ a : ↥A,
      algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a =
        constantsHom N A a := fun a => rfl

  have hconst_adj : ∀ (g : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : ↥A),
      constantsHom N A a ∈ (Algebra.adjoin (AlgebraicClosure ℚ) ({g} :
        Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))).toSubring :=
    fun g a => Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
  refine ⟨?_, ?_⟩
  ·
    refine assemble N ℓ A (chartAlgFin N ℓ) ψF hinjF hICF ?_ hcT fm.BFin (affineBaseFin N A) ?_ (CharPModel.jBar N)
      (jChartFin N ℓ) (Subtype.ext rfl) le_rfl Subring.subset_closure ?_ fm.integralFin hmemF fm.constFin_mem
      hspanF fm.piFin ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ fm.jBar_mem fm.piFin_j
      fm.piFin_const fm.ker_piFin fm.intClosed_piFin hEq _ (Subtype.ext rfl)
    · intro a b
      apply Subtype.ext
      exact hψF a b
    · rw [affineBaseFin, Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact fm.constFin_mem a
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact fm.jBar_mem
    · rw [affineBaseFin, Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact hconst_adj _ a
      · rw [Set.mem_singleton_iff] at hy; subst hy
        exact Algebra.subset_adjoin rfl
  ·
    have hb₀ : embS N ℓ (chartAlgInf N ℓ) (jInvChartInf N ℓ) = (CharPModel.jBar N)⁻¹ := by
      apply Subtype.ext
      change coeffEmb (AlgebraicClosure ℚ) ((((jFull N)⁻¹ : ↥(modularFunctionFieldFull N)) :
        LaurentSeries ℚ)) = ((CharPModel.jBar N : ↥(laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹
      rw [IntermediateField.coe_inv, map_inv₀]
      rfl
    have hhF : (IntermediateField.equivOfEq hEq).symm
        ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
          ↥(modularFunctionFieldC (ResidueField ↥A) N))⁻¹) =
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
          ↥(modularFunctionFieldFullC (ResidueField ↥A) N))⁻¹ := by
      rw [map_inv₀]
      rfl
    refine assemble N ℓ A (chartAlgInf N ℓ) ψI hinjI hICI ?_ hcT fm.BInf (affineBaseInf N A) ?_ (CharPModel.jBar N)⁻¹
      (jInvChartInf N ℓ) hb₀ le_rfl Subring.subset_closure ?_ fm.integralInf hmemI fm.constInf_mem
      hspanI fm.piInf _ fm.jInvBar_mem fm.piInf_jInv
      fm.piInf_const fm.ker_piInf fm.intClosed_piInf hEq _ hhF
    · intro a b
      apply Subtype.ext
      exact hψI a b
    · rw [affineBaseInf, Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact fm.constInf_mem a
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact fm.jInvBar_mem
    · rw [affineBaseInf, Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact hconst_adj _ a
      · rw [Set.mem_singleton_iff] at hy; subst hy
        exact Algebra.subset_adjoin rfl

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme.FibreIsoK"

end S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing (solution)
