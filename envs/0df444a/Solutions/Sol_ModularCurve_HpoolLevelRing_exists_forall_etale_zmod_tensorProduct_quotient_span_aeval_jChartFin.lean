-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2b0a99fd-cb7f-5861-8cbf-7edf77c7610d

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
import Theorems.Thm_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem
import Theorems.Thm_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin
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

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open scoped TensorProduct
p2m_open "Polynomial P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin.Polynomial ModularCurve AlgebraicCurve"

namespace Polynomial p2m_export "Polynomial" "C X aeval_map_algebraMap aeval_def C_eq_algebraMap leadingCoeff coeff aeval aeval_C map_map map Monic comp roots algebra Separable eq_prod_roots_of_splits_id isUnit_C dvd_iff_isRoot mod eval_map ext mapRingHom IsRoot ring aeval_algHom_apply leadingCoeff_ne_zero" end Polynomial
p2m_open_scoped "Polynomial" in

theorem Polynomial.exists_ne_zero_dvd_map_of_isAlgClosed_of_isAlgebraic
    (k₀ k : Type*) [Field k₀] [Field k] [Algebra k₀ k] [IsAlgClosed k] [Algebra.IsAlgebraic k₀ k]
    (c : k[X]) (hc : c ≠ 0) :
    ∃ d : k₀[X], d ≠ 0 ∧ c ∣ d.map (algebraMap k₀ k) := by
  classical
  set d : k₀[X] := (c.roots.map fun r => minpoly k₀ r).prod with hd
  have hd0 : d ≠ 0 := by
    rw [hd]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp h
    exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral r) hr
  refine ⟨d, hd0, ?_⟩

  have hsplit : c = C c.leadingCoeff * (c.roots.map fun r => X - C r).prod :=
    (Polynomial.Splits.eq_prod_roots (IsAlgClosed.splits c)).trans (by simp)
  have hdvd : (c.roots.map fun r => X - C r).prod ∣ d.map (algebraMap k₀ k) := by
    rw [hd, Polynomial.map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_dvd_prod_of_dvd _ _ fun r _ => ?_
    show X - C r ∣ (minpoly k₀ r).map (algebraMap k₀ k)
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval k₀ r
  have hunit : IsUnit (C c.leadingCoeff) := Polynomial.isUnit_C.mpr (leadingCoeff_ne_zero.mpr hc).isUnit
  rw [hsplit]
  exact (hunit.mul_left_dvd).mpr hdvd

namespace LevelL

noncomputable def zmodAlgEquivIntQuotient (n : ℕ) : ZMod n ≃ₐ[ℤ] ℤ ⧸ Ideal.span {(n : ℤ)} :=
  AlgEquiv.ofRingEquiv (f := (Int.quotientSpanNatEquivZMod n).symm) (fun x => by simp)

noncomputable def zmodTensorAlgEquivQuotient (n : ℕ) (B : Type*) [CommRing B] :
    ZMod n ⊗[ℤ] B ≃ₐ[ℤ] B ⧸ Ideal.span {(n : B)} :=
  (Algebra.TensorProduct.congr (zmodAlgEquivIntQuotient n) (AlgEquiv.refl (R := ℤ) (A₁ := B))).trans <|
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (Ideal.span {(n : ℤ)})).restrictScalars ℤ).symm.trans <|
      Ideal.quotientEquivAlgOfEq ℤ (by rw [Ideal.map_span, Set.image_singleton, map_natCast])

@[scoped simp] theorem zmodTensorAlgEquivQuotient_one_tmul (n : ℕ) (B : Type*) [CommRing B] (b : B) :
    zmodTensorAlgEquivQuotient n B (1 ⊗ₜ b) = Ideal.Quotient.mk _ b := by
  have h1 : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (Ideal.span {(n : ℤ)})).symm (1 ⊗ₜ[ℤ] b) =
      Ideal.Quotient.mk _ b := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  simp [zmodTensorAlgEquivQuotient, zmodAlgEquivIntQuotient, h1]

theorem zmodTensorAlgEquivQuotient_tmul (n : ℕ) (B : Type*) [CommRing B] (a : ZMod n) (b : B) :
    zmodTensorAlgEquivQuotient n B (a ⊗ₜ b) = Ideal.Quotient.mk _ ((a.cast : ℤ) • b) := by
  have : a ⊗ₜ[ℤ] b = ((a.cast : ℤ) : ZMod n) ⊗ₜ[ℤ] b := by rw [ZMod.intCast_zmod_cast]
  rw [this, ← zsmul_one ((a.cast : ℤ)), TensorProduct.smul_tmul]
  exact zmodTensorAlgEquivQuotient_one_tmul n B _

namespace D1

universe u

theorem etale_quotient_span_singleton_of_equiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Type u) [CommRing C] [Algebra k C] (c : C)
    (B : Type u) [CommRing B] [Algebra K B]
    (Ψ : K ⊗[k] C ≃ₐ[K] B)
    (hB : Algebra.Etale K (B ⧸ Ideal.span {Ψ ((1 : K) ⊗ₜ[k] c)})) :
    Algebra.Etale k (C ⧸ Ideal.span {c}) := by
  have e1 : K ⊗[k] (C ⧸ Ideal.span {c}) ≃ₐ[K]
      (K ⊗[k] C) ⧸ (Ideal.span {c}).map (Algebra.TensorProduct.includeRight (A := K) (R := k)) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := k) K C K (Ideal.span {c})
  have hIJ : Ideal.span {Ψ ((1 : K) ⊗ₜ[k] c)} =
      ((Ideal.span {c}).map (Algebra.TensorProduct.includeRight (A := K) (R := k))).map
        (Ψ : K ⊗[k] C →+* B) := by
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have e2 := Ideal.quotientEquivAlg
    ((Ideal.span {c}).map (Algebra.TensorProduct.includeRight (A := K) (R := k)))
    (Ideal.span {Ψ ((1 : K) ⊗ₜ[k] c)}) Ψ hIJ
  haveI : Algebra.Etale K (K ⊗[k] (C ⧸ Ideal.span {c})) := Algebra.Etale.of_equiv (e1.trans e2).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat K

theorem not_mem_of_isCoprime_of_dvd_of_span_le_comap
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {h c d : R} (hcop : IsCoprime h d) (hcd : c ∣ d)
    (P : Ideal B) [P.IsPrime] (hle : Ideal.span {h} ≤ P.comap (algebraMap R B)) :
    algebraMap R B c ∉ P := by
  intro hc
  have hc' : c ∈ P.comap (algebraMap R B) := hc
  have hd : d ∈ P.comap (algebraMap R B) := Ideal.mem_of_dvd _ hcd hc'
  have hh : h ∈ P.comap (algebraMap R B) := hle (Ideal.mem_span_singleton_self h)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : R) ∈ P.comap (algebraMap R B) := by
    rw [← huv]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hh) (Ideal.mul_mem_left _ _ hd)
  exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h1)

theorem congr_refl_trans_tmul {k K C D B : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    [Semiring C] [Algebra k C] [Semiring D] [Algebra k D] [Semiring B] [Algebra K B]
    (br : D ≃ₐ[k] C) (e : K ⊗[k] C ≃ₐ[K] B) (x : K) (y : D) :
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) br).trans e) (x ⊗ₜ y) = e (x ⊗ₜ br y) := rfl

theorem ringHom_apply_algebraMap_zmod {n : ℕ} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra (ZMod n) A] [Algebra (ZMod n) B] (f : A →+* B) (x : ZMod n) :
    f (algebraMap (ZMod n) A x) = algebraMap (ZMod n) B x :=
  RingHom.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod n) A)) (algebraMap (ZMod n) B)) x

def algEquivOfRingEquivZMod {n : ℕ} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra (ZMod n) A] [Algebra (ZMod n) B] (e : A ≃+* B) : A ≃ₐ[ZMod n] B :=
  AlgEquiv.ofRingEquiv (f := e) (fun x => ringHom_apply_algebraMap_zmod e.toRingHom x)

@[scoped simp] theorem algEquivOfRingEquivZMod_apply {n : ℕ} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra (ZMod n) A] [Algebra (ZMod n) B] (e : A ≃+* B) (a : A) :
    algEquivOfRingEquivZMod (n := n) e a = e a := rfl

section Assembly

open ModularCurve.HpoolLevelRing

variable (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]

@[reducible] noncomputable def zmodAlgebraQuot : Algebra (ZMod ℓ) (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)}) :=
  ((zmodTensorAlgEquivQuotient ℓ (Afin p)).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ZMod ℓ) (B := Afin p))).toAlgebra

attribute [local instance] zmodAlgebraQuot

omit [NeZero p] in

noncomputable def bridge : (ZMod ℓ ⊗[ℤ] Afin p) ≃ₐ[ZMod ℓ] (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)}) :=
  algEquivOfRingEquivZMod (zmodTensorAlgEquivQuotient ℓ (Afin p)).toRingEquiv

omit [NeZero p] in
theorem bridge_one_tmul (a : Afin p) :
    bridge p ℓ ((1 : ZMod ℓ) ⊗ₜ[ℤ] a) = Ideal.Quotient.mk _ a := by
  show zmodTensorAlgEquivQuotient ℓ (Afin p) _ = _
  exact zmodTensorAlgEquivQuotient_one_tmul ℓ (Afin p) a

abbrev B0 (K : Type) [Field K] : Type :=
  ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p)))

noncomputable abbrev jbar (K : Type) [Field K] : B0 p K :=
  ⟨⟨jqModC K, jqModC_mem_full K p⟩, CurveModel.adjoin_le_chartRing K _ (Algebra.self_mem_adjoin_singleton K _)⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_forall_etale_of_chartFibre (hℓ : ℓ ≠ p)
    (K : Type) [Field K] [CharP K ℓ] [IsAlgClosed K] [Algebra (ZMod ℓ) K] [Algebra.IsAlgebraic (ZMod ℓ) K]
    (e : K ⊗[ZMod ℓ] (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)}) ≃ₐ[K] B0 p K)
    (he : (e ((1 : K) ⊗ₜ[ZMod ℓ] Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : Afin p)})
          (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).1 =
        (⟨jqModC K, jqModC_mem_full K p⟩ : ↥(modularFunctionFieldFullC K p))) :
    ∃ avoid : (ZMod ℓ)[X], avoid ≠ 0 ∧
      ∀ g : ℤ[X], (g.map (Int.castRingHom (ZMod ℓ))).Separable →
        IsCoprime (g.map (Int.castRingHom (ZMod ℓ))) avoid →
        Algebra.Etale (ZMod ℓ) ((ZMod ℓ ⊗[ℤ] Afin p) ⧸
          Ideal.span {(1 : ZMod ℓ) ⊗ₜ[ℤ] Polynomial.aeval (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) := by
  classical
  letI algKX : Algebra K[X] (B0 p K) := (Polynomial.aeval (R := K) (jbar p K)).toRingHom.toAlgebra
  have halg : ∀ q : K[X], algebraMap K[X] (B0 p K) q = Polynomial.aeval (jbar p K) q := fun q => rfl
  haveI : IsScalarTower K K[X] (B0 p K) :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [halg, ← Polynomial.C_eq_algebraMap, Polynomial.aeval_C]

  obtain ⟨hD, hF, hT, hS⟩ := ModularCurve.isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC p ℓ hℓ K
  haveI := hD; haveI := hF; haveI := hT
  haveI : Module.IsTorsionFree K[X] (B0 p K) := inferInstance
  haveI : FaithfulSMul K[X] (B0 p K) := inferInstance
  haveI : Algebra.IsSeparable (FractionRing K[X]) (FractionRing (B0 p K)) := hS

  obtain ⟨c, hc0, hc⟩ := IsDedekindDomain.exists_ne_zero_forall_isUnramifiedAt_of_notMem K[X] (B0 p K)

  obtain ⟨d, hd0, hcd⟩ := Polynomial.exists_ne_zero_dvd_map_of_isAlgClosed_of_isAlgebraic (ZMod ℓ) K c hc0
  refine ⟨d, hd0, fun g hsep hcop => ?_⟩

  set h : K[X] := (g.map (Int.castRingHom (ZMod ℓ))).map (algebraMap (ZMod ℓ) K) with hh
  have hmap : h = g.map (algebraMap ℤ K) := by
    rw [hh, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
  have hsep' : h.Separable := hsep.map
  have hcop' : IsCoprime h (d.map (algebraMap (ZMod ℓ) K)) := hcop.map (Polynomial.mapRingHom (algebraMap (ZMod ℓ) K))
  have hunr : ∀ (P : Ideal (B0 p K)) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap K[X] (B0 p K)) → Algebra.IsUnramifiedAt K[X] P :=
    fun P _ _ hle => hc P (not_mem_of_isCoprime_of_dvd_of_span_le_comap hcop' hcd P hle)

  have hG := IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt (B0 p K) h hsep' hunr

  let Ψ : K ⊗[ZMod ℓ] (ZMod ℓ ⊗[ℤ] Afin p) ≃ₐ[K] B0 p K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) (bridge p ℓ)).trans e

  let φ : Afin p →+* B0 p K :=
    (e : K ⊗[ZMod ℓ] (Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)}) →+* B0 p K).comp
      ((Algebra.TensorProduct.includeRight (R := ZMod ℓ) (A := K)
          (B := Afin p ⧸ Ideal.span {((ℓ : ℕ) : Afin p)})).toRingHom.comp (Ideal.Quotient.mk _))
  have hΨ : ∀ a : Afin p, Ψ ((1 : K) ⊗ₜ[ZMod ℓ] ((1 : ZMod ℓ) ⊗ₜ[ℤ] a)) = φ a := fun a => by
    show ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) (bridge p ℓ)).trans e) _ = _
    rw [congr_refl_trans_tmul, bridge_one_tmul]
    rfl
  have hφj : φ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = jbar p K :=
    Subtype.ext he
  have hΨg : Ψ ((1 : K) ⊗ₜ[ZMod ℓ] ((1 : ZMod ℓ) ⊗ₜ[ℤ]
      Polynomial.aeval (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g)) =
      Polynomial.aeval (jbar p K) g := by
    rw [hΨ, ← hφj, ← RingHom.toIntAlgHom_apply φ, ← Polynomial.aeval_algHom_apply, RingHom.toIntAlgHom_apply]
  have hideal : Ideal.map (algebraMap K[X] (B0 p K)) (Ideal.span {h}) =
      Ideal.span {Ψ ((1 : K) ⊗ₜ[ZMod ℓ] ((1 : ZMod ℓ) ⊗ₜ[ℤ]
        Polynomial.aeval (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g))} := by
    rw [Ideal.map_span, Set.image_singleton, hΨg, halg, hmap, Polynomial.aeval_map_algebraMap]
  haveI : Algebra.Etale K (B0 p K ⧸ Ideal.span {Ψ ((1 : K) ⊗ₜ[ZMod ℓ] ((1 : ZMod ℓ) ⊗ₜ[ℤ]
      Polynomial.aeval (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g))}) :=
    hideal ▸ hG
  exact etale_quotient_span_singleton_of_equiv (ZMod ℓ) K (ZMod ℓ ⊗[ℤ] Afin p) _ (B0 p K) Ψ this

end Assembly

end D1
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin.LevelL.D1"
end LevelL
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin.LevelL.D1 P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin.LevelL"

open IsLocalRing ModularCurve.HpoolLevelRing in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    ∃ avoid : (ZMod ℓ)[X], avoid ≠ 0 ∧
      ∀ g : ℤ[X], g.Monic → (g.map (Int.castRingHom (ZMod ℓ))).Separable →
        IsCoprime (g.map (Int.castRingHom (ZMod ℓ))) avoid →
        Algebra.Etale (ZMod ℓ) ((ZMod ℓ ⊗[ℤ] Afin p) ⧸
          Ideal.span {(1 : ZMod ℓ) ⊗ₜ[ℤ] Polynomial.aeval (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI : CharP (ResidueField ↥A) ℓ := ValuationSubring.charP_residueField_of_liesOverPrime ℓ A hA
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  letI : Algebra (ZMod ℓ) (ResidueField ↥A) := ZMod.algebra _ ℓ
  obtain ⟨eK⟩ :=
    ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A (q := ℓ) hA
  haveI : Algebra.IsAlgebraic (ZMod ℓ) (ResidueField ↥A) :=
    (LevelL.D1.algEquivOfRingEquivZMod (n := ℓ) eK).symm.isAlgebraic
  letI := LevelL.D1.zmodAlgebraQuot p ℓ
  obtain ⟨e, he⟩ :=
    ModularCurve.HpoolLevelRing.exists_algEquiv_residueField_tensor_quotient_span_natCast_chartRing p ℓ hℓ A hA
  obtain ⟨avoid, h0, H⟩ := LevelL.D1.exists_forall_etale_of_chartFibre p ℓ hℓ (ResidueField ↥A) e he
  exact ⟨avoid, h0, fun g _ hsep hcop => H g hsep hcop⟩

end S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin (solution)
