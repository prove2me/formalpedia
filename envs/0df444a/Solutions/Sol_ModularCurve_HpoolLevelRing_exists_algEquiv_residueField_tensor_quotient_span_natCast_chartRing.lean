-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/defb50d4-871d-5d86-8dd5-394fbd9f0981

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing
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

open scoped TensorProduct
open Polynomial IsLocalRing ModularCurve ModularCurve.HpoolLevelRing ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve

namespace LevelL
namespace ChartFibre

abbrev D (ℓ : ℕ) (K B : Type) [CommRing K] [CommRing B] [Algebra (ZMod ℓ) K]
    [Algebra (ZMod ℓ) (B ⧸ Ideal.span {((ℓ : ℕ) : B)})] : Type :=
  K ⊗[ZMod ℓ] (B ⧸ Ideal.span {((ℓ : ℕ) : B)})

section Generic

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (K : Type) [Field K] [CharP K ℓ] [Algebra (ZMod ℓ) K]
variable (Z : Type) [CommRing Z] [Algebra Z K]
variable (B : Type) [CommRing B] [Algebra (ZMod ℓ) (B ⧸ Ideal.span {((ℓ : ℕ) : B)})]
variable (M : Type) [CommRing M] [Algebra Z M] (e₂ : Z ⊗[ℤ] B ≃ₐ[Z] M)

set_option linter.unusedSectionVars false

noncomputable def toC : B →+* K ⊗[Z] M :=
  (Algebra.TensorProduct.includeRight (R := Z) (A := K) (B := M)).toRingHom.comp
    (e₂.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := Z) (B := B)).toRingHom)

theorem toC_apply (b : B) : toC K Z B M e₂ b = (1 : K) ⊗ₜ[Z] e₂ ((1 : Z) ⊗ₜ[ℤ] b) := rfl

theorem toC_natCast_ell : toC K Z B M e₂ ((ℓ : ℕ) : B) = 0 := by
  rw [map_natCast, ← map_natCast (algebraMap K (K ⊗[Z] M)) ℓ, CharP.cast_eq_zero K ℓ, map_zero]

theorem toC_vanishes (b : B) (hb : b ∈ Ideal.span {((ℓ : ℕ) : B)}) : toC K Z B M e₂ b = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [map_mul, toC_natCast_ell ℓ K Z B M e₂, mul_zero]

noncomputable def quotToC₀ : (B ⧸ Ideal.span {((ℓ : ℕ) : B)}) →+* K ⊗[Z] M :=
  Ideal.Quotient.lift (Ideal.span {((ℓ : ℕ) : B)}) (toC K Z B M e₂) (toC_vanishes ℓ K Z B M e₂)

theorem quotToC₀_mk (b : B) :
    quotToC₀ ℓ K Z B M e₂ (Ideal.Quotient.mk _ b) = (1 : K) ⊗ₜ[Z] e₂ ((1 : Z) ⊗ₜ[ℤ] b) := rfl

noncomputable def quotToC : (B ⧸ Ideal.span {((ℓ : ℕ) : B)}) →ₐ[ZMod ℓ] K ⊗[Z] M where
  toRingHom := quotToC₀ ℓ K Z B M e₂
  commutes' r := RingHom.congr_fun (Subsingleton.elim ((quotToC₀ ℓ K Z B M e₂).comp (algebraMap (ZMod ℓ) _))
      (algebraMap (ZMod ℓ) (K ⊗[Z] M))) r

theorem quotToC_mk (b : B) :
    quotToC ℓ K Z B M e₂ (Ideal.Quotient.mk _ b) = (1 : K) ⊗ₜ[Z] e₂ ((1 : Z) ⊗ₜ[ℤ] b) := rfl

noncomputable def fwd : D ℓ K B →ₐ[K] K ⊗[Z] M :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K ⊗[Z] M)) (quotToC ℓ K Z B M e₂) (fun x y => Commute.all _ _)

theorem fwd_tmul (x : K) (b : B) :
    fwd ℓ K Z B M e₂ (x ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk _ b) = x ⊗ₜ[Z] e₂ ((1 : Z) ⊗ₜ[ℤ] b) := by
  rw [fwd, Algebra.TensorProduct.lift_tmul, quotToC_mk, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, mul_one]

noncomputable def toD₀ : B →+* D ℓ K B :=
  (Algebra.TensorProduct.includeRight (R := ZMod ℓ) (A := K) (B := B ⧸ Ideal.span {((ℓ : ℕ) : B)})).toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : B)}))

theorem toD₀_apply (b : B) : toD₀ ℓ K B b = (1 : K) ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk _ b := rfl

instance : IsScalarTower ℤ Z (D ℓ K B) := AddCommGroup.intIsScalarTower (R := Z) (M := D ℓ K B)

noncomputable def midToD : Z ⊗[ℤ] B →ₐ[Z] D ℓ K B :=
  Algebra.TensorProduct.lift (Algebra.ofId Z (D ℓ K B)) ((toD₀ ℓ K B).toIntAlgHom) (fun x y => Commute.all _ _)

theorem midToD_tmul (z : Z) (b : B) :
    midToD ℓ K Z B (z ⊗ₜ[ℤ] b) = algebraMap Z K z ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk _ b := by
  rw [midToD, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  show algebraMap Z (D ℓ K B) z * toD₀ ℓ K B b = _
  rw [toD₀_apply, IsScalarTower.algebraMap_apply Z K (D ℓ K B), Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, mul_one]

noncomputable def bwd : K ⊗[Z] M →ₐ[K] D ℓ K B :=
  Algebra.TensorProduct.lift (Algebra.ofId K (D ℓ K B)) ((midToD ℓ K Z B).comp e₂.symm.toAlgHom)
    (fun x y => Commute.all _ _)

theorem bwd_tmul (x : K) (z : Z) (b : B) :
    bwd ℓ K Z B M e₂ (x ⊗ₜ[Z] e₂ (z ⊗ₜ[ℤ] b)) = (x * algebraMap Z K z) ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk _ b := by
  rw [bwd, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
    AlgEquiv.symm_apply_apply, midToD_tmul, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self, RingHom.id_apply, one_mul]

theorem bwd_fwd : (bwd ℓ K Z B M e₂).comp (fwd ℓ K Z B M e₂) = AlgHom.id K (D ℓ K B) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AlgHom.ext
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.id_apply]
    rw [fwd_tmul, bwd_tmul, map_one, mul_one]

theorem fwd_bwd : (fwd ℓ K Z B M e₂).comp (bwd ℓ K Z B M e₂) = AlgHom.id K (K ⊗[Z] M) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  ·
    have key : ∀ m : M, (fwd ℓ K Z B M e₂) ((bwd ℓ K Z B M e₂) ((1 : K) ⊗ₜ[Z] m)) = (1 : K) ⊗ₜ[Z] m := by
      intro m
      obtain ⟨t, rfl⟩ := e₂.surjective m
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul z b =>
        rw [bwd_tmul, one_mul, fwd_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← map_smul e₂,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add s t hs ht => simp only [map_add, TensorProduct.tmul_add, hs, ht]
    apply AlgHom.ext
    intro m
    simpa using key m

noncomputable def equiv : D ℓ K B ≃ₐ[K] K ⊗[Z] M :=
  AlgEquiv.ofAlgHom (fwd ℓ K Z B M e₂) (bwd ℓ K Z B M e₂) (fwd_bwd ℓ K Z B M e₂) (bwd_fwd ℓ K Z B M e₂)

theorem equiv_tmul_mk (x : K) (b : B) :
    equiv ℓ K Z B M e₂ (x ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk _ b) = x ⊗ₜ[Z] e₂ ((1 : Z) ⊗ₜ[ℤ] b) :=
  fwd_tmul ℓ K Z B M e₂ x b

end Generic

end LevelL.ChartFibre

section Main

open LevelL.ChartFibre

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    [Algebra (ZMod ℓ) (ResidueField ↥A)] [Algebra (ZMod ℓ) (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)})] :
    ∃ e : ResidueField ↥A ⊗[ZMod ℓ] (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)}) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A)
          ({⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) p⟩} :
            Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))),
      (e ((1 : ResidueField ↥A) ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : Afin p)})
          (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).1 =
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) p⟩ :
          ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) := by
  classical

  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime ℓ A hA
  letI : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra

  have hℓprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime))
  haveI := hℓprime
  haveI : IsLocalization (Ideal.span {(ℓ : ℤ)}).primeCompl ↥(GaloisRep.ratLocalizedAt ℓ) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : ℓ.Prime)

  obtain ⟨e₂, he₂⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg ℤ
    ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull p) (Ideal.span {(ℓ : ℤ)}).primeCompl
    {IgusaScheme.jFull p}
  have e₂' : ↥(GaloisRep.ratLocalizedAt ℓ) ⊗[ℤ] Afin p ≃ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ) := e₂

  obtain ⟨⟨eFin, heFin⟩, -⟩ :=
    ModularCurve.IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing p ℓ
      (fun h => hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)) A hA ρ hρ

  refine ⟨(equiv ℓ (ResidueField ↥A) ↥(GaloisRep.ratLocalizedAt ℓ) (Afin p) ↥(chartAlgFin p ℓ) e₂).trans eFin, ?_⟩
  rw [AlgEquiv.trans_apply, equiv_tmul_mk]
  have hj : e₂ ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ]
      AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) =
      jChartFin p ℓ := by
    apply Subtype.ext
    rw [he₂, one_smul]
    rfl
  erw [hj]
  exact heFin

end Main

end S_ModularCurve_HpoolLevelRing_exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing (solution)
