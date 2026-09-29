-- Prove2me | solution 1 for ModularCurve.reductionModL_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e266c500-5070-57c4-930c-98523879329b

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL
import Theorems.Thm_AlgebraicCurve_ConstantReduction_placeMap_surjective
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionModL_surjective
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply"
p2m_attr_erase "simp" "ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsPlaceReductionAlong PrincipalGeneratedByIntegral coe_reductionDegZeroAlong IsPlaceReductionModL ReductionInputsModL placeReductionModL isPlaceReductionModL_placeReductionModL reductionModL reductionModL_mk IsPlaceReductionAlong.eq_of_agree modularFunctionFieldBar JZero qExpand_one_apply jq modularFunctionFieldFull jqd_mem_full coeffMap coeffEmb_mem_laurentBaseChange coeffMap_jqModC jqModC_ne_zero_of_nontrivial modularFunctionFieldFullC jqModC_mem_full jqModC jqModC_rat exists_constantReduction_isGood_isPlaceReductionModL reductionInputsModL_of_not_dvd isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC JZero.divisible transcendental_jqModC finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi dedekindPsi_pos"
namespace M8Surj
p2m_open "ModularCurve~jq_mem_full"

p2m_open "AlgebraicCurve ModularCurve~jq_mem_full P2MW.S_ModularCurve_reductionModL_surjective.ModularCurve HahnSeries IntermediateField IsLocalRing"

local notation "Qb" => AlgebraicClosure ℚ

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (IsLocalRing.residue A) hsurj p
    exact ⟨q, hq⟩
  obtain ⟨q, hqp, hdeg, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hdegL : (q.map (algebraMap A L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A L),
      Polynomial.degree_eq_natDegree hqmonic.ne_zero, hdeg]
    exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirr)).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap A L)) hdegL
  have hyint : IsIntegral A y :=
    ⟨q, hqmonic, by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hy⟩
  obtain ⟨a, rfl⟩ : ∃ a : A, algebraMap A L a = y := IsIntegrallyClosed.isIntegral_iff.mp hyint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hqa : q.eval a = 0 := by
    have h := hy
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom] at h
    exact (IsFractionRing.injective A L) (h.trans (map_zero _).symm)
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_hom, hqa, map_zero]

theorem degree_eq_zero_of_mem_principal {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this, hdeg]

theorem degree_mapDomain_of_deg_eq' {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F'] (s : Place K F → Place K' F') (hs : ∀ P, (s P).deg = P.deg)
    (D : Divisor K F) : Divisor.degree (Finsupp.mapDomain s D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, hs]

section NonConst

variable {A : ValuationSubring Qb} {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem jq_mem_full : jq ∈ modularFunctionFieldFull N := by
  have h := jqd_mem_full N (one_dvd N)
  rwa [qExpand_one_apply] at h

omit [NeZero N] in
theorem jqModC_mem_bar : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N := by
  rw [coeffMap_jqModC, ← coeffMap_jqModC (algebraMap ℚ Qb), jqModC_rat]
  exact coeffEmb_mem_laurentBaseChange Qb (jq_mem_full (N := N))

def jF (A : ValuationSubring Qb) (N : ℕ) : modularFunctionFieldBar N :=
  ⟨coeffMap A.subtype (jqModC A), jqModC_mem_bar⟩

omit [NeZero N] in
theorem jF_ne_zero : jF A N ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val h
  change coeffMap A.subtype (jqModC A) = 0 at h1
  rw [coeffMap_jqModC] at h1
  exact jqModC_ne_zero_of_nontrivial Qb h1

theorem exists_principal_mapDomain_ne_zero [IsAlgClosed (ResidueField A)]
    [HasPrincipalDivisors Qb (modularFunctionFieldBar N)] (hNk : (N : ResidueField A) ≠ 0)
    {r : Place Qb (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)}
    (hr : IsPlaceReductionModL A N r) :
    ∃ D ∈ Divisor.principal (K := Qb) (F := modularFunctionFieldBar N), Finsupp.mapDomain r D ≠ 0 := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := Qb) (jF A N) jF_ne_zero
  refine ⟨D, ⟨jF A N, jF_ne_zero, hD⟩, fun h0 => ?_⟩
  have hyk : coeffMap (IsLocalRing.residue A) (jqModC A) ∈ modularFunctionFieldFullC (ResidueField A) N := by
    rw [coeffMap_jqModC]; exact jqModC_mem_full _ N
  have hne : coeffMap (IsLocalRing.residue A) (jqModC A) ≠ 0 := by
    rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial _
  set jb : modularFunctionFieldFullC (ResidueField A) N := ⟨coeffMap (IsLocalRing.residue A) (jqModC A), hyk⟩
    with hjbdef
  have hord : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N), Q.ord jb = 0 := by
    intro Q
    rw [← hr.2 (jqModC A) jqModC_mem_bar hyk hne D hD Q, h0, Finsupp.zero_apply]
  have hjb : jb = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :=
    Subtype.ext (coeffMap_jqModC _)
  have htr : Transcendental (ResidueField A) jb := by
    rw [hjb, ← transcendental_algebraMap_iff
      (algebraMap (modularFunctionFieldFullC (ResidueField A) N) (LaurentSeries (ResidueField A))).injective]
    exact transcendental_jqModC (ResidueField A)
  haveI : FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({jb} : Set (modularFunctionFieldFullC (ResidueField A) N)))
      (modularFunctionFieldFullC (ResidueField A) N) := by
    apply Module.finite_of_finrank_pos
    rw [hjb, finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ResidueField A) N hNk]
    exact dedekindPsi_pos N (NeZero.ne N)
  obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed jb htr hord
  exact htr (hc ▸ isAlgebraic_algebraMap c)

end NonConst

theorem main (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring Qb) (hA : A.LiesOverPrime ℓ) :
    Function.Surjective (reductionModL A N) := by
  haveI : IsAlgClosed (ResidueField A) := isAlgClosed_residueField A
  haveI : CharP (ResidueField A) ℓ :=
    ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  have hNk : (N : ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ResidueField A) ℓ N]
    exact hℓN

  have h : ReductionInputsModL A N := reductionInputsModL_of_not_dvd N hℓN A hA
  obtain ⟨R, -, hR⟩ := exists_constantReduction_isGood_isPlaceReductionModL N hℓN A hA

  haveI : IsCurveOver Qb (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : HasPrincipalDivisors Qb (modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldFullC _ N
  have hdeg : ∀ P : Place Qb (modularFunctionFieldBar N), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdeg' : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N), Q.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdiv := JZero.divisible N
  have hprin0 : ∀ D ∈ Divisor.principal (K := Qb) (F := modularFunctionFieldBar N),
      Divisor.degree D = 0 := fun D hD => degree_eq_zero_of_mem_principal hD
  have hρ : IsPlaceReductionModL A N (placeReductionModL h) := isPlaceReductionModL_placeReductionModL h
  have hgen : PrincipalGeneratedByIntegral A (IsLocalRing.residue A) N := h.choose_spec.2

  have hρr : placeReductionModL h = R.placeMap := by
    refine IsPlaceReductionAlong.eq_of_agree hgen (fun D hD => ?_) hdeg hprin0 hdiv
      (exists_principal_mapDomain_ne_zero hNk hρ)
    obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
    ext Q
    rw [hρ.2 y hy hyk hne D hDy Q, hR.2 y hy hyk hne D hDy Q]

  have hsurj : Function.Surjective R.placeMap := ConstantReduction.placeMap_surjective R
  set s := Function.surjInv hsurj with hs
  have hrs : ∀ Q, R.placeMap (s Q) = Q := Function.surjInv_eq hsurj

  intro y
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
  set D : Divisor Qb (modularFunctionFieldBar N) :=
    Finsupp.mapDomain s (E : Divisor (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)) with hD
  have hD0 : D ∈ Divisor.degZero (K := Qb) (F := modularFunctionFieldBar N) := by
    rw [Divisor.mem_degZero, hD, degree_mapDomain_of_deg_eq' s (fun Q => by rw [hdeg, hdeg'])]
    exact Divisor.mem_degZero.mp E.2
  refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
  rw [reductionModL_mk h]
  congr 1
  apply Subtype.ext
  rw [coe_reductionDegZeroAlong, hρr]
  change Finsupp.mapDomain R.placeMap (Finsupp.mapDomain s (E : Divisor (ResidueField A)
    (modularFunctionFieldFullC (ResidueField A) N))) = E
  rw [← Finsupp.mapDomain_comp]
  have hid : (R.placeMap ∘ s) = id := funext hrs
  rw [hid, Finsupp.mapDomain_id]

end ModularCurve.M8Surj

end

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    Function.Surjective (ModularCurve.reductionModL A N) :=
  ModularCurve.M8Surj.main N hℓN A hA

end S_ModularCurve_reductionModL_surjective
end P2MW
export P2MW.S_ModularCurve_reductionModL_surjective (solution)
