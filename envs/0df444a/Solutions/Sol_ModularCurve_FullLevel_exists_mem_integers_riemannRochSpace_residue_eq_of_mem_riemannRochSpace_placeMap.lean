-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fc815e21-15e1-5c03-99ac-8833748b9eaa

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_transcendental_residue_finrank_adjoin_eq_of_isGood
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_P2M_Dup_ModularCurve_deg_eq_one_modularFunctionFieldC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing

namespace SepL

section Transport
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem transport_of_eq {E₁ E₂ : IntermediateField K L} (h : E₁ = E₂) :
    (IsCurveOver K ↥E₂ → IsCurveOver K ↥E₁) ∧
    (Algebra.EssFiniteType K ↥E₂ → Algebra.EssFiniteType K ↥E₁) ∧
    genusFF K ↥E₁ = genusFF K ↥E₂ := by
  subst h
  exact ⟨id, id, rfl⟩

end Transport

section RR
variable (k F : Type*) [Field k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem finrank_riemannRochSpace_eq [IsAlgClosed k] (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (Module.finrank k ↥(riemannRochSpace D) : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by
  obtain ⟨t, ht, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  exact AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable k t ht hfin hsep D hD

theorem finiteDimensional_riemannRochSpace (P : Place k F) (D : Divisor k F) :
    FiniteDimensional k ↥(riemannRochSpace D) := by
  haveI : Nonempty (Place k F) := ⟨P⟩
  haveI : FiniteDimensional k ↥(LSpace (0 : Divisor k F)) := AlgebraicCurve.finiteDimensional_lSpace_zero k F
  exact AlgebraicCurve.finiteDimensional_lSpace D

end RR

section MapDomain
variable {α β : Type*} (r : α → β)

theorem mapDomain_apply_nonneg (E : α →₀ ℤ) (hE : ∀ a, 0 ≤ E a) (Q : β) : 0 ≤ Finsupp.mapDomain r E Q := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_nonneg fun a _ => ?_
  show (0 : ℤ) ≤ (Finsupp.single (r a) (E a)) Q
  rw [Finsupp.single_apply]
  split_ifs
  · exact hE a
  · exact le_rfl

theorem neg_smul_single_le_mapDomain (D : α →₀ ℤ) (P₀ : α) (n : ℕ)
    (hD : ∀ P, -(((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) P) ≤ D P) (Q : β) :
    -(((n : ℤ) • Finsupp.single (r P₀) (1 : ℤ)) Q) ≤ Finsupp.mapDomain r D Q := by
  set D' : α →₀ ℤ := -((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) with hD'
  have h1 : ∀ a, 0 ≤ (D - D') a := fun a => by
    rw [Finsupp.sub_apply, sub_nonneg, hD', Finsupp.neg_apply]
    exact hD a
  have h2 := mapDomain_apply_nonneg r (D - D') h1 Q
  have h3 : Finsupp.mapDomain r (D - D') = Finsupp.mapDomain r D - Finsupp.mapDomain r D' :=
    map_sub (Finsupp.mapDomain.addMonoidHom r) D D'
  have h4 : Finsupp.mapDomain r D' = -((n : ℤ) • Finsupp.single (r P₀) (1 : ℤ)) := by
    rw [hD']
    change Finsupp.mapDomain.addMonoidHom r (-((n : ℤ) • Finsupp.single P₀ (1 : ℤ))) = _
    rw [map_neg, map_zsmul]
    change -((n : ℤ) • Finsupp.mapDomain r (Finsupp.single P₀ (1 : ℤ))) = _
    rw [Finsupp.mapDomain_single]
  rw [h3, h4, Finsupp.sub_apply, Finsupp.neg_apply] at h2
  linarith

end MapDomain

end SepL

open SepL

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (P₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (n : ℕ)
    (hn : 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ≤ n + 1)
    (g : modularFunctionFieldC (ResidueField A) M')
    (hg : g ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ))) :
    ∃ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) ∧ R₀.residue ⟨f, hf⟩ = g := by
  classical

  haveI hκac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hκch : CharP (ResidueField ↥A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  have hM'κ : ((M' : ℕ) : (ResidueField ↥A)) ≠ 0 := fun h =>
    hqM' ((CharP.cast_eq_zero_iff (ResidueField ↥A) q M').mp h)
  have heqF : modularFunctionFieldC (ResidueField ↥A) M' = modularFunctionFieldFullC (ResidueField ↥A) M' :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) q M' hqM'
  obtain ⟨hIC, hEF, hgen⟩ := transport_of_eq (K := (ResidueField ↥A)) heqF
  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := hIC (isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) M')
  haveI : Algebra.EssFiniteType (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := hEF (essFiniteType_modularFunctionFieldFullC (ResidueField ↥A) M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := isCurveOver_modularFunctionFieldBar M'
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := essFiniteType_modularFunctionFieldBar M'
  have hgenus : genusFF (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    hgen.trans (genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar (ResidueField ↥A) M' hM'κ)
  have hGood : R₀.IsGood := hgenus
  haveI hVfd : FiniteDimensional (AlgebraicClosure ℚ)
      ↥(riemannRochSpace ((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) :=
    finiteDimensional_riemannRochSpace (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') P₀ _
  haveI hVbarfd : FiniteDimensional (ResidueField ↥A)
      ↥(riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) : Submodule (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')) :=
    finiteDimensional_riemannRochSpace (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (R₀.placeMap P₀) _

  let T : Set ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    {h | ∃ f : ↥R₀.integers, (f : ↥(modularFunctionFieldBar M')) ∈ (riemannRochSpace ((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) :
      Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) ∧ R₀.residue f = h}
  let W : Submodule (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    { carrier := T
      zero_mem' := ⟨0, Submodule.zero_mem _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨f, hfV, rfl⟩ ⟨g', hgV, rfl⟩
        exact ⟨f + g', Submodule.add_mem _ hfV hgV, map_add _ _ _⟩
      smul_mem' := by
        rintro c _ ⟨f, hfV, rfl⟩
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ), (R₀.algebraMap_mem_iff _).mpr a.2⟩ * f,
          ?_, ?_⟩
        · show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ) * (f : ↥(modularFunctionFieldBar M')) ∈ _
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ hfV
        · rw [map_mul, R₀.residue_algebraMap, Algebra.smul_def] }
  have hspanT : Submodule.span (ResidueField ↥A) T = W :=
    le_antisymm (Submodule.span_le.mpr fun h hh => hh) fun h hh => Submodule.subset_span hh

  have hF : ∃ x : ↥(modularFunctionFieldBar M'), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(modularFunctionFieldBar M'))) ↥(modularFunctionFieldBar M') := by
    obtain ⟨t, ht, hfin, -⟩ :=
      AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M'))
    exact ⟨t, ht, hfin⟩
  obtain ⟨x, hxT, hxpos, hxdeg⟩ :=
    AlgebraicCurve.ConstantReduction.exists_transcendental_residue_finrank_adjoin_eq_of_isGood A ↥(modularFunctionFieldBar M') hF ↥(modularFunctionFieldC (ResidueField ↥A) M') R₀ hGood
  have hL1 : Module.finrank (ResidueField ↥A) ↥(Submodule.span (ResidueField ↥A) T) =
      Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace ((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) :
        Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) :=
    AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R₀.toRegularProlongation x hxT hxpos hxdeg _
  rw [hspanT] at hL1

  have hWle : W ≤ riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) := by
    rintro _ ⟨f, hfV, rfl⟩
    by_cases hres : R₀.residue f = 0
    · rw [hres]; exact Submodule.zero_mem _
    have hf0 : (f : ↥(modularFunctionFieldBar M')) ≠ 0 := by
      intro h0
      apply hres
      have : f = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (f : ↥(modularFunctionFieldBar M')) hf0
    have hlaw := R₀.mapDomain_placeMap f hres D hD
    rw [mem_riemannRochSpace_iff]
    intro Qpl
    right
    rw [← hlaw Qpl]
    apply neg_smul_single_le_mapDomain
    intro P
    rw [hD P]
    rcases (mem_riemannRochSpace_iff.mp hfV) P with h0 | h
    · exact absurd h0 hf0
    · exact h

  have hdegV : Divisor.degree ((n : ℤ) • Finsupp.single P₀ (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) = n := by
    rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar M' P₀]
    simp
  have hdegVbar : Divisor.degree ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ) : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')) = n := by
    rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldC (ResidueField ↥A) M' (R₀.placeMap P₀)]
    simp
  have hrrV := finrank_riemannRochSpace_eq (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')
    ((n : ℤ) • Finsupp.single P₀ (1 : ℤ)) (by rw [hdegV]; omega)
  have hrrVbar := finrank_riemannRochSpace_eq (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')
    ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) (by rw [hdegVbar, hgenus]; omega)
  rw [hdegV] at hrrV
  rw [hdegVbar, hgenus] at hrrVbar
  have hfin_eq : Module.finrank (ResidueField ↥A) ↥W =
      Module.finrank (ResidueField ↥A) ↥(riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) :
        Submodule (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')) := by
    have h1 : (Module.finrank (ResidueField ↥A) ↥W : ℤ) =
        Module.finrank (ResidueField ↥A) ↥(riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) :
          Submodule (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')) := by
      rw [hL1, hrrV, hrrVbar]
    exact_mod_cast h1
  have hWeq : W = riemannRochSpace ((n : ℤ) • Finsupp.single (R₀.placeMap P₀) (1 : ℤ)) :=
    Submodule.eq_of_le_of_finrank_eq hWle hfin_eq

  have hgW : g ∈ W := by rw [hWeq]; exact hg
  obtain ⟨f, hfV, hfg⟩ := hgW
  exact ⟨f, f.2, hfV, hfg⟩

end S_ModularCurve_FullLevel_exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap (solution)
