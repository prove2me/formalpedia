-- Prove2me | solution 1 for ModularCurve.exists_constantReduction_chartData_of_isEmbBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a7b4e247-4415-569f-a0a7-516c6c998132

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_span_residue_eq_riemannRochSpace_of_isEmbBasis_of_isGood
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem
import Theorems.Thm_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring
import Theorems.Thm_ModularCurve_exists_finset_linearIndependent_residue_coeff
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

open AlgebraicCurve ModularCurve

set_option autoImplicit false

open AlgebraicCurve

noncomputable section

namespace P2MChartData

variable {k : Type*} [Field k] {Fbar : Type*} [Field Fbar] [Algebra k Fbar]

theorem ord_ge_of_mem {D' : Divisor k Fbar} {u : Fbar} (hu : u ∈ riemannRochSpace D') (hu0 : u ≠ 0)
    (Q : Place k Fbar) : -D' Q ≤ Q.ord u :=
  ((mem_riemannRochSpace_iff.mp hu) Q).resolve_left hu0

theorem ne_zero_of_notMem {D' : Divisor k Fbar} {u : Fbar} (hu : u ∉ riemannRochSpace D') : u ≠ 0 := by
  intro h0; apply hu; rw [h0]; exact zero_mem _

theorem ord_lt_of_mem_notMem {D' : Divisor k Fbar} {u : Fbar} (Q : Place k Fbar)
    (hu : u ∈ riemannRochSpace D') (hu' : u ∉ riemannRochSpace (D' - Finsupp.single Q 1)) :
    Q.ord u < -D' Q + 1 := by
  classical
  by_contra hge
  push Not at hge
  apply hu'
  rw [mem_riemannRochSpace_iff]
  intro v
  by_cases hv : v = Q
  · subst hv; right
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]; linarith
  · rcases (mem_riemannRochSpace_iff.mp hu) v with h | h
    · exact Or.inl h
    · right
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]; exact h

theorem evalAt_smul_of_mem (Q : Place k Fbar) (hQ : Q.IsRational) (a : k) {f : Fbar}
    (hf : f ∈ Q.toValuationSubring) : Q.evalAt (a • f) = a * Q.evalAt f := by
  rw [Algebra.smul_def, Q.evalAt_mul_of_mem hQ (Q.algebraMap_mem' a) hf, Q.evalAt_algebraMap_eq]

theorem evalAt_add_of_mem (Q : Place k Fbar) (hQ : Q.IsRational) {f g : Fbar}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f + g) = Q.evalAt f + Q.evalAt g := by
  apply Q.algebraMap_residueField_injective
  rw [map_add, Q.algebraMap_evalAt hQ (add_mem hf hg), Q.algebraMap_evalAt hQ hf, Q.algebraMap_evalAt hQ hg,
    ← map_add]
  rfl

theorem evalAt_sum_smul (Q : Place k Fbar) (hQ : Q.IsRational) {r : ℕ} (cf : Fin r → k) (f : Fin r → Fbar)
    (hf : ∀ i, f i ∈ Q.toValuationSubring) (T : Finset (Fin r)) :
    (∑ i ∈ T, cf i • f i) ∈ Q.toValuationSubring ∧
      Q.evalAt (∑ i ∈ T, cf i • f i) = ∑ i ∈ T, cf i * Q.evalAt (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [Finset.sum_empty]
    have : Q.evalAt (0 : Fbar) = Q.evalAt (algebraMap k Fbar 0) := by rw [map_zero]
    rw [this, Q.evalAt_algebraMap_eq]
  | insert a T ha ih =>
    have hsm : cf a • f a ∈ Q.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' _) (hf a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨add_mem hsm ih.1, ?_⟩
    rw [evalAt_add_of_mem Q hQ hsm ih.1, evalAt_smul_of_mem Q hQ (cf a) (hf a), ih.2]

theorem ord_eq_zero_of_evalAt_ne_zero (Q : Place k Fbar) (hQ : Q.IsRational) {f : Fbar}
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f ≠ 0) : Q.ord f = 0 := by
  have hres : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := Q.ord_coe_unit u
  rwa [hu] at this

theorem ord_nonneg_of_mem (Q : Place k Fbar) {f : Fbar} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : Fbar) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

theorem evalAt_eq_zero_of_ord_pos (Q : Place k Fbar) (hQ : Q.IsRational) {f : Fbar}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have := ord_eq_zero_of_evalAt_ne_zero Q hQ hf hne
  omega

theorem chartData_of_span_of_rrDrop {r : ℕ} (hr0 : 0 < r)
    (D : Divisor k Fbar) (hD : ∀ Q, 0 ≤ D Q) (xb : Fin r → Fbar)
    (hspan : Submodule.span k (Set.range xb) = riemannRochSpace D)
    (hbpf : ∀ Q : Place k Fbar, Q.IsRational →
      ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single Q 1))
    (hdrop : ∀ P Q : Place k Fbar, P.IsRational → Q.IsRational →
      ∃ u ∈ riemannRochSpace (D - Finsupp.single P 1),
        u ∉ riemannRochSpace (D - Finsupp.single P 1 - Finsupp.single Q 1)) :
    ∃ cQ iQ : Place k Fbar → Fin r,
      (∀ Q : Place k Fbar, Q.IsRational → xb (cQ Q) ≠ 0 ∧ Q.ord (xb (cQ Q)) = -(D Q)) ∧
      (∀ Q : Place k Fbar, Q.IsRational →
        Q.ord (xb (iQ Q) * (xb (cQ Q))⁻¹
          - algebraMap k Fbar (Q.evalAt (xb (iQ Q) * (xb (cQ Q))⁻¹))) = 1) ∧
      (∀ Q Q' : Place k Fbar, Q.IsRational → Q'.IsRational → Q' ≠ Q →
        Q'.ord (xb (cQ Q)) = -(D Q') →
        ∃ j, Q.evalAt (xb j * (xb (cQ Q))⁻¹) ≠ Q'.evalAt (xb j * (xb (cQ Q))⁻¹)) := by
  classical

  have hxbD : ∀ i, xb i ∈ riemannRochSpace D := fun i => by
    rw [← hspan]; exact Submodule.subset_span ⟨i, rfl⟩

  have key : ∀ Q : Place k Fbar, Q.IsRational →
      ∃ i, xb i ∉ riemannRochSpace (D - Finsupp.single Q 1) := by
    intro Q hQ
    by_contra hall
    push Not at hall
    obtain ⟨u, hu, hu'⟩ := hbpf Q hQ
    apply hu'
    have : riemannRochSpace D ≤ riemannRochSpace (D - Finsupp.single Q 1) := by
      rw [← hspan]; exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    exact this hu

  let cQ : Place k Fbar → Fin r := fun Q =>
    if h : ∃ i, xb i ∉ riemannRochSpace (D - Finsupp.single Q 1) then Classical.choose h else ⟨0, hr0⟩
  have hcQ : ∀ Q : Place k Fbar, Q.IsRational → xb (cQ Q) ≠ 0 ∧ Q.ord (xb (cQ Q)) = -(D Q) := by
    intro Q hQ
    have h := key Q hQ
    have hc : xb (cQ Q) ∉ riemannRochSpace (D - Finsupp.single Q 1) := by
      show xb (if h : ∃ i, xb i ∉ riemannRochSpace (D - Finsupp.single Q 1) then Classical.choose h else ⟨0, hr0⟩) ∉ _
      rw [dif_pos h]; exact Classical.choose_spec h
    have h0 := ne_zero_of_notMem hc
    refine ⟨h0, le_antisymm ?_ (ord_ge_of_mem (hxbD _) h0 Q)⟩
    have := ord_lt_of_mem_notMem Q (hxbD _) hc
    omega

  have hSreg : ∀ (Q P : Place k Fbar), Q.IsRational → P.ord (xb (cQ Q)) = -(D P) →
      ∀ j, xb j * (xb (cQ Q))⁻¹ ∈ P.toValuationSubring := by
    intro Q P hQ hP j
    have hc0 := (hcQ Q hQ).1
    rcases eq_or_ne (xb j) 0 with hj | hj
    · rw [hj, zero_mul]; exact zero_mem _
    · apply P.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hj (inv_ne_zero hc0))
      rw [P.ord_mul hj (inv_ne_zero hc0), P.ord_inv, hP]
      linarith [ord_ge_of_mem (hxbD j) hj P]

  have hcomb : ∀ u ∈ riemannRochSpace D, ∃ cf : Fin r → k, u = ∑ i, cf i • xb i := by
    intro u hu
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨cf, hcf⟩ := hu
    exact ⟨cf, hcf.symm⟩

  have htanex : ∀ Q : Place k Fbar, Q.IsRational → ∃ j,
      Q.ord (xb j * (xb (cQ Q))⁻¹ - algebraMap k Fbar (Q.evalAt (xb j * (xb (cQ Q))⁻¹))) = 1 := by
    intro Q hQ
    obtain ⟨hc0, hcord⟩ := hcQ Q hQ
    set g := xb (cQ Q) with hg
    set S : Fin r → Fbar := fun j => xb j * g⁻¹ with hS
    have hSmem : ∀ j, S j ∈ Q.toValuationSubring := fun j => hSreg Q Q hQ hcord j
    set n : Fin r → Fbar := fun j => S j - algebraMap k Fbar (Q.evalAt (S j)) with hn
    have hnmem : ∀ j, n j ∈ Q.toValuationSubring := fun j => sub_mem (hSmem j) (Q.algebraMap_mem' _)
    have hnval : ∀ j, Q.evalAt (n j) = 0 := by
      intro j
      show Q.evalAt (S j - algebraMap k Fbar (Q.evalAt (S j))) = 0
      have : S j - algebraMap k Fbar (Q.evalAt (S j)) = S j + (-(Q.evalAt (S j))) • (1 : Fbar) := by
        rw [Algebra.smul_def, mul_one, map_neg, sub_eq_add_neg]
      rw [this, evalAt_add_of_mem Q hQ (hSmem j) (by rw [Algebra.smul_def, mul_one]; exact Q.algebraMap_mem' _),
        evalAt_smul_of_mem Q hQ _ (one_mem _), Q.evalAt_one]; ring

    obtain ⟨u, hu, hu'⟩ := hdrop Q Q hQ hQ
    have hu0 := ne_zero_of_notMem hu'
    have huD : u ∈ riemannRochSpace D := by
      apply lSpace_mono (D := D - Finsupp.single Q 1) (E := D) _ hu
      intro v; rw [Finsupp.sub_apply, Finsupp.single_apply]; split_ifs <;> linarith
    have hordu : Q.ord u = -(D Q) + 1 := by
      have h1 := ord_ge_of_mem hu hu0 Q
      have h2 := ord_lt_of_mem_notMem Q hu hu'
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at h1 h2
      omega
    set t := u * g⁻¹ with ht
    have ht0 : t ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hc0)
    have htord : Q.ord t = 1 := by rw [ht, Q.ord_mul hu0 (inv_ne_zero hc0), Q.ord_inv, hordu, hcord]; ring
    have htmem : t ∈ Q.toValuationSubring := Q.mem_toValuationSubring_of_ord_nonneg_alt ht0 (by omega)
    have htinv : ∀ j, n j * t⁻¹ ∈ Q.toValuationSubring := by
      intro j
      rcases eq_or_ne (n j) 0 with h0 | h0
      · rw [h0, zero_mul]; exact zero_mem _
      · apply Q.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero h0 (inv_ne_zero ht0))
        rw [Q.ord_mul h0 (inv_ne_zero ht0), Q.ord_inv, htord]
        have : 0 < Q.ord (n j) := by
          by_contra hle; push Not at hle
          have h00 := ord_nonneg_of_mem Q h0 (hnmem j)
          have : Q.ord (n j) = 0 := by omega
          exact (Q.evalAt_ne_zero_of_ord_eq_zero hQ h0 this) (hnval j)
        omega

    by_contra hnone
    push Not at hnone

    have hm0 : ∀ j, Q.evalAt (n j * t⁻¹) = 0 := by
      intro j
      by_contra hne
      apply hnone j
      show Q.ord (n j) = 1
      have hnj0 : n j ≠ 0 := by
        intro h0; apply hne; rw [h0, zero_mul]
        have : Q.evalAt (0 : Fbar) = Q.evalAt (algebraMap k Fbar 0) := by rw [map_zero]
        rw [this, Q.evalAt_algebraMap_eq]
      have h0ord := ord_eq_zero_of_evalAt_ne_zero Q hQ (htinv j) hne
      rw [Q.ord_mul hnj0 (inv_ne_zero ht0), Q.ord_inv, htord] at h0ord
      omega
    obtain ⟨cf, hcf⟩ := hcomb u huD
    have htsum : t = ∑ j, cf j • S j := by
      rw [ht, hcf, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; rw [hS, smul_mul_assoc]

    have hval_t : Q.evalAt t = 0 := evalAt_eq_zero_of_ord_pos Q hQ htmem (by omega)
    have hsumA : ∑ j, cf j * Q.evalAt (S j) = 0 := by
      rw [← (evalAt_sum_smul Q hQ cf S hSmem Finset.univ).2, ← htsum, hval_t]

    have hnsum : ∑ j, cf j • n j = t := by
      have : ∑ j, cf j • n j = ∑ j, cf j • S j - algebraMap k Fbar (∑ j, cf j * Q.evalAt (S j)) := by
        rw [map_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _
        show cf j • (S j - algebraMap k Fbar (Q.evalAt (S j))) = _
        rw [smul_sub, map_mul, Algebra.smul_def, Algebra.smul_def]
      rw [this, hsumA, map_zero, sub_zero, ← htsum]

    have hone : ∑ j, cf j • (n j * t⁻¹) = 1 := by
      have : ∑ j, cf j • (n j * t⁻¹) = (∑ j, cf j • n j) * t⁻¹ := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; rw [smul_mul_assoc]
      rw [this, hnsum, mul_inv_cancel₀ ht0]
    have := (evalAt_sum_smul Q hQ cf (fun j => n j * t⁻¹) htinv Finset.univ).2
    rw [hone, Q.evalAt_one] at this
    simp only [hm0, mul_zero, Finset.sum_const_zero] at this
    exact one_ne_zero this
  let iQ : Place k Fbar → Fin r := fun Q =>
    if h : ∃ j, Q.ord (xb j * (xb (cQ Q))⁻¹ - algebraMap k Fbar (Q.evalAt (xb j * (xb (cQ Q))⁻¹))) = 1
    then Classical.choose h else ⟨0, hr0⟩
  refine ⟨cQ, iQ, hcQ, ?_, ?_⟩
  · intro Q hQ
    have h := htanex Q hQ
    have hiQ : iQ Q = Classical.choose h := by
      show (if h : ∃ j, Q.ord (xb j * (xb (cQ Q))⁻¹ - algebraMap k Fbar (Q.evalAt (xb j * (xb (cQ Q))⁻¹))) = 1
        then Classical.choose h else ⟨0, hr0⟩) = Classical.choose h
      rw [dif_pos h]
    rw [hiQ]; exact Classical.choose_spec h
  ·
    intro Q Q' hQ hQ' hne hguard
    obtain ⟨hc0, hcord⟩ := hcQ Q hQ
    set g := xb (cQ Q) with hg
    set S : Fin r → Fbar := fun j => xb j * g⁻¹ with hS
    have hSQ : ∀ j, S j ∈ Q.toValuationSubring := fun j => hSreg Q Q hQ hcord j
    have hSQ' : ∀ j, S j ∈ Q'.toValuationSubring := fun j => hSreg Q Q' hQ hguard j
    obtain ⟨u, hu, hu'⟩ := hdrop Q Q' hQ hQ'
    have hu0 := ne_zero_of_notMem hu'
    have huD : u ∈ riemannRochSpace D := by
      apply lSpace_mono (D := D - Finsupp.single Q 1) (E := D) _ hu
      intro v; rw [Finsupp.sub_apply, Finsupp.single_apply]; split_ifs <;> linarith

    have hQu : -(D Q) + 1 ≤ Q.ord u := by
      have := ord_ge_of_mem hu hu0 Q
      rwa [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl, neg_sub, sub_eq_neg_add] at this
    have hQ'u : Q'.ord u = -(D Q') := by
      have h1 := ord_ge_of_mem hu hu0 Q'
      have h2 := ord_lt_of_mem_notMem Q' hu hu'
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg hne.symm, sub_zero] at h1 h2
      omega
    set t := u * g⁻¹ with ht
    have ht0 : t ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hc0)
    have htQ : 0 < Q.ord t := by rw [ht, Q.ord_mul hu0 (inv_ne_zero hc0), Q.ord_inv, hcord]; omega
    have htQ' : Q'.ord t = 0 := by rw [ht, Q'.ord_mul hu0 (inv_ne_zero hc0), Q'.ord_inv, hQ'u, hguard]; ring
    have htmemQ : t ∈ Q.toValuationSubring := Q.mem_toValuationSubring_of_ord_nonneg_alt ht0 htQ.le
    have htmemQ' : t ∈ Q'.toValuationSubring := Q'.mem_toValuationSubring_of_ord_nonneg_alt ht0 htQ'.ge
    have hvQ : Q.evalAt t = 0 := evalAt_eq_zero_of_ord_pos Q hQ htmemQ htQ
    have hvQ' : Q'.evalAt t ≠ 0 := Q'.evalAt_ne_zero_of_ord_eq_zero hQ' ht0 htQ'
    obtain ⟨cf, hcf⟩ := hcomb u huD
    have htsum : t = ∑ j, cf j • S j := by
      rw [ht, hcf, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; rw [hS, smul_mul_assoc]
    by_contra hall
    push Not at hall
    apply hvQ'
    rw [htsum, (evalAt_sum_smul Q' hQ' cf S hSQ' Finset.univ).2]
    rw [htsum, (evalAt_sum_smul Q hQ cf S hSQ Finset.univ).2] at hvQ
    rw [← hvQ]
    apply Finset.sum_congr rfl; intro j _; rw [hall j]

end P2MChartData

end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MDock

open IsLocalRing HahnSeries

section ofRP

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def ofRegularProlongation (R : RegularProlongation A F Fbar)
    (r : Place L F → Place (ResidueField A) Fbar) (hdeg : ∀ P, (r P).deg = P.deg)
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F,
      (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f)) :
    ConstantReduction A F Fbar where
  integers := R.integers
  residue := R.residue
  placeMap := r
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  deg_placeMap := hdeg
  mapDomain_placeMap := hdiv

theorem residue_mul_inv_eq (R : ConstantReduction A F Fbar) {a b : F} (ha : a ∈ R.integers)
    (hb : b ∈ R.integers) (hab : a * b⁻¹ ∈ R.integers) (hbres : R.residue ⟨b, hb⟩ ≠ 0) :
    R.residue ⟨a * b⁻¹, hab⟩ = R.residue ⟨a, ha⟩ * (R.residue ⟨b, hb⟩)⁻¹ := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hbres
    have : (⟨(0 : F), hb⟩ : R.integers) = 0 := rfl
    rw [this, map_zero]
  rw [eq_mul_inv_iff_mul_eq₀ hbres, ← map_mul]
  congr 1
  apply Subtype.ext
  show a * b⁻¹ * b = a
  rw [inv_mul_cancel_right₀ hb0]

end ofRP

theorem forall_coeff_mem_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : LaurentSeries (AlgebraicClosure ℚ)) :
    (∀ k : ℤ, x.coeff k ∈ A) ↔ ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  constructor
  · intro h
    refine ⟨⟨fun k => ⟨x.coeff k, h k⟩, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro k hk
      rw [HahnSeries.mem_support]
      exact fun h0 => hk (Subtype.ext h0)
    · ext k
      rfl
  · rintro ⟨y, rfl⟩ k
    rw [coeffMap_coeff]
    exact (y.coeff k).2

def coeffLinearMap (k : Type*) [Field k] (E : IntermediateField k (LaurentSeries k)) :
    E →ₗ[k] (ℤ → k) where
  toFun x n := (x : LaurentSeries k).coeff n
  map_add' x y := by funext n; simp
  map_smul' c x := by
    funext n
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [IntermediateField.coe_smul, Algebra.smul_def]
    have halg : algebraMap k (LaurentSeries k) c = HahnSeries.single 0 c := by
      rw [show algebraMap k (LaurentSeries k) c
          = HahnSeries.ofPowerSeries ℤ k (PowerSeries.C c) from rfl,
        HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
    rw [halg, HahnSeries.coeff_single_zero_mul]

theorem coeffLinearMap_apply (k : Type*) [Field k] (E : IntermediateField k (LaurentSeries k))
    (x : E) (n : ℤ) : coeffLinearMap k E x n = (x : LaurentSeries k).coeff n := rfl

theorem exists_mem_notMem_of_finrank_ne {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
    (D : Divisor k Fbar) (Q : Place k Fbar)
    (h : Module.finrank k (riemannRochSpace D) ≠
      Module.finrank k (riemannRochSpace (D - Finsupp.single Q 1))) :
    ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single Q 1) := by
  classical
  have hle : riemannRochSpace (D - Finsupp.single Q 1) ≤ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : riemannRochSpace (D - Finsupp.single Q 1) ≠ riemannRochSpace D := by
    intro heq
    exact h (by rw [heq])
  obtain ⟨u, hu, hnu⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨u, hu, hnu⟩

theorem one_mem_riemannRochSpace_of_nonneg {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
    (D : Divisor k Fbar) (hD : ∀ Q, 0 ≤ D Q) : (1 : Fbar) ∈ riemannRochSpace D := by
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rw [Place.ord_one]
  linarith [hD v]

theorem one_mem_notMem_of_apply_eq_zero {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
    (D : Divisor k Fbar) (hD : ∀ Q, 0 ≤ D Q) (Q : Place k Fbar) (hQ : D Q = 0) :
    ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single Q 1) := by
  refine ⟨1, one_mem_riemannRochSpace_of_nonneg D hD, ?_⟩
  · intro h
    rw [mem_riemannRochSpace_iff] at h
    rcases h Q with h0 | h1
    · exact one_ne_zero h0
    · rw [Finsupp.sub_apply, Finsupp.single_eq_same, hQ, Place.ord_one] at h1
      omega

end P2MDock

end

open P2MDock IsLocalRing in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime → ℓ ∉ S →
      A.LiesOverPrime ℓ →
      ∃ (Fbar : Type) (_ : Field Fbar) (_ : Algebra (IsLocalRing.ResidueField A) Fbar)
        (R : ConstantReduction A (modularFunctionFieldBar N) Fbar) (hx : ∀ i, s i ∈ R.integers)
        (cQ iQ : Place (IsLocalRing.ResidueField A) Fbar → Fin r),
        R.IsGood ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.IsRational ∧ (R.placeMap P).IsRational) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          R.residue ⟨s (cQ (R.placeMap P)), hx _⟩ ≠ 0 ∧
          (R.placeMap P).ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          ∀ hmem : s (iQ (R.placeMap P)) * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          (R.placeMap P).ord (R.residue ⟨_, hmem⟩
            - algebraMap (IsLocalRing.ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨_, hmem⟩))) = 1) ∧
        (∀ P P' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap P' ≠ R.placeMap P →
          (R.placeMap P').ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P')) →
          ∀ hmem : ∀ j, s j * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          ∃ j, (R.placeMap P).evalAt (R.residue ⟨_, hmem j⟩) ≠ (R.placeMap P').evalAt (R.residue ⟨_, hmem j⟩)) := by
  classical
  obtain ⟨S₁, hS₁, h1⟩ := exists_finset_forall_coeff_mem_valuationSubring N s
  obtain ⟨S₂, hS₂, h2⟩ := exists_finset_linearIndependent_residue_coeff N s hs.1
  refine ⟨N.primeFactors ∪ S₁ ∪ S₂, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact hS₁ p hp
    · exact hS₂ p hp
  intro A ℓ hℓ hℓS hA
  simp only [Finset.mem_union, not_or] at hℓS
  obtain ⟨⟨hℓN', hℓ1⟩, hℓ2⟩ := hℓS
  have hℓN : ¬ ℓ ∣ N := fun hd => hℓN' (Nat.mem_primeFactors.mpr ⟨hℓ, hd, NeZero.ne N⟩)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  haveI hkac : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField A) ℓ := ValuationSubring.residueField_charP_of_liesOverPrime A hℓ hA
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldFullC (ResidueField A) N
  have hNk : ((N : ℕ) : ResidueField A) ≠ 0 := fun h =>
    hℓN ((CharP.cast_eq_zero_iff (ResidueField A) ℓ N).mp h)

  have hdeg_up : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.deg = 1 :=
    fun P => deg_eq_one_modularFunctionFieldBar N P
  have hdeg_down : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N), Q.deg = 1 :=
    fun Q => IsCurveOver.deg_eq_one_of_isAlgClosed Q
  have hrat_up : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.IsRational :=
    fun P => (Place.isRational_iff_deg_eq_one P).mpr (hdeg_up P)
  have hrat_down : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N), Q.IsRational :=
    fun Q => (Place.isRational_iff_deg_eq_one Q).mpr (hdeg_down Q)

  obtain ⟨RP, rmap, hdock, hdiv⟩ :=
    exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd N ℓ hℓN A hA
  let R : ConstantReduction A (modularFunctionFieldBar N) (modularFunctionFieldFullC (ResidueField A) N) :=
    ofRegularProlongation RP rmap (fun P => by rw [hdeg_up, hdeg_down]) hdiv
  have hgood : R.IsGood := (ConstantReduction.isGood_iff R).mpr
    (genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar (ResidueField A) N hNk)

  have hint' : ∀ (i : Fin r) (n : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff n) ∈ A :=
    h1 ℓ hℓ hℓ1 A hA
  have hy' : ∀ i, ∃ y : LaurentSeries A, coeffMap A.subtype y = (s i : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun i => (forall_coeff_mem_iff A _).mp (hint' i)
  choose y hy using hy'
  have key : ∀ i, ∃ hxi : s i ∈ R.integers,
      ((R.residue ⟨s i, hxi⟩ : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) (y i) := by
    intro i
    have aux : ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (y i) →
        ∃ hxi : x ∈ R.integers,
          ((R.residue ⟨x, hxi⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) (y i) := by
      rintro ⟨x, hxm⟩ (rfl : x = coeffMap A.subtype (y i))
      exact hdock (y i) hxm
    exact aux (s i) (hy i).symm
  choose hx hres using key

  have hcoeffy : ∀ i n, (y i).coeff n = ⟨(s i : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hint' i n⟩ := by
    intro i n
    apply Subtype.ext
    show A.subtype ((y i).coeff n) = (s i : LaurentSeries (AlgebraicClosure ℚ)).coeff n
    rw [← coeffMap_coeff A.subtype (y i) n, hy i]
  have hli : LinearIndependent (ResidueField A) fun i => R.residue ⟨s i, hx i⟩ := by
    have h2' := h2 ℓ hℓ hℓ2 A hA hint'
    refine LinearIndependent.of_comp
      (coeffLinearMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)) ?_
    convert h2' using 1
    funext i n
    rw [Function.comp_apply, coeffLinearMap_apply, hres i, coeffMap_coeff, hcoeffy]

  have hspan := span_residue_eq_riemannRochSpace_of_isEmbBasis_of_isGood N A R hgood s hs hx hli
  have hdrop := fun (P Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
      (hP : P.IsRational) (hQ : Q.IsRational) =>
    exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem N A R hgood P Q hP hQ

  have hE : embDivisor N = Finsupp.single (cuspInftyBar N) (embDegree N : ℤ) := by
    rw [embDivisor, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hDeq : Finsupp.mapDomain R.placeMap (embDivisor N)
      = Finsupp.single (R.placeMap (cuspInftyBar N)) (embDegree N : ℤ) := by
    rw [hE, Finsupp.mapDomain_single]
  have hD0 : ∀ Q, 0 ≤ Finsupp.mapDomain R.placeMap (embDivisor N) Q := by
    intro Q
    rw [hDeq, Finsupp.single_apply]
    split_ifs
    · exact Int.natCast_nonneg _
    · exact le_rfl

  have hbpf : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N), Q.IsRational →
      ∃ u ∈ riemannRochSpace (Finsupp.mapDomain R.placeMap (embDivisor N)),
        u ∉ riemannRochSpace (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single Q 1) := by
    intro Q _
    by_cases hQ : Finsupp.mapDomain R.placeMap (embDivisor N) Q = 0
    · exact one_mem_notMem_of_apply_eq_zero _ hD0 Q hQ
    ·
      have hQc : R.placeMap (cuspInftyBar N) = Q := by
        by_contra hne
        apply hQ
        rw [hDeq, Finsupp.single_apply, if_neg hne]
      apply exists_mem_notMem_of_finrank_ne
      set g := genusFF (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) with hg
      have hgg : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) = g := hgood.symm
      have hdegD : Divisor.degree (Finsupp.mapDomain R.placeMap (embDivisor N)) = 2 * (g : ℤ) + 1 := by
        rw [hDeq, Divisor.degree_single, hdeg_down, embDegree, hgg]
        push_cast
        ring
      have hdegD' : Divisor.degree (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single Q 1)
          = 2 * (g : ℤ) := by
        rw [map_sub, hdegD, Divisor.degree_single, hdeg_down]
        push_cast
        ring
      have e1 := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC (ResidueField A) N
        (Finsupp.mapDomain R.placeMap (embDivisor N)) (by rw [hdegD]; omega)
      have e2 := ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC (ResidueField A) N
        (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single Q 1) (by rw [hdegD']; omega)
      rw [hdegD] at e1
      rw [hdegD'] at e2
      intro heq
      have : (ell (Finsupp.mapDomain R.placeMap (embDivisor N)) : ℤ)
          = (ell (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single Q 1) : ℤ) := by
        unfold ell LSpace
        exact_mod_cast heq
      omega

  have hr0 : 0 < r := by
    by_contra hr
    have hr' : r = 0 := by omega
    subst hr'
    have h1m := one_mem_riemannRochSpace_of_nonneg _ hD0
    rw [← hspan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at h1m
    exact one_ne_zero h1m

  obtain ⟨cQ, iQ, hii, hiii, hiv⟩ := P2MChartData.chartData_of_span_of_rrDrop hr0
    (Finsupp.mapDomain R.placeMap (embDivisor N)) hD0 (fun i => R.residue ⟨s i, hx i⟩) hspan hbpf hdrop
  refine ⟨modularFunctionFieldFullC (ResidueField A) N, inferInstance, inferInstance, R, hx, cQ, iQ,
    hgood, fun P => ⟨hrat_up P, hrat_down _⟩, fun P => hii _ (hrat_down _), ?_, ?_⟩
  · intro P hmem
    rw [residue_mul_inv_eq R (hx _) (hx _) hmem (hii _ (hrat_down _)).1]
    exact hiii _ (hrat_down _)
  · intro P P' hne hguard hmem
    obtain ⟨j, hj⟩ := hiv (R.placeMap P) (R.placeMap P') (hrat_down _) (hrat_down _) hne hguard
    refine ⟨j, ?_⟩
    rw [residue_mul_inv_eq R (hx _) (hx _) (hmem j) (hii _ (hrat_down _)).1]
    exact hj

end S_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis
end P2MW
export P2MW.S_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis (solution)
