-- Prove2me | solution 1 for ModularCurve.tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d687be2f-5005-5afc-b3f0-797672115245

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ModularCurve_tateModule_eq_zero_of_forall_frobenius_smul_smul_eq
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Theorems.Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Pic.baseChange_mk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

open ModularCurve AlgebraicCurve

namespace FrobeniusEigenvalueTateModule

private theorem w_pairing
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] :
    ∃ B : TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]]
        ℤ_[p],
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : TateModule p (ModularCurve.JZero M)),
        B (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
            (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              y) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B x y) ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      (∀ y, (∀ x, B x y = 0) → y = 0) :=
  ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul p M

private theorem w_cycloChar
    (m : ℕ)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
        cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓm) :=
  ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt m cyc hcyc ℓ hℓ hℓm

private theorem w_frobenius_sq
    (N₀ : ℕ) [NeZero N₀] {p : ℕ} [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (x : _root_.TateModule q (JZero N₀))
    (hx : ∀ n : ℕ, σ • σ • (x : ℕ → JZero N₀) n = (x : ℕ → JZero N₀) n) :
    x = 0 :=
  ModularCurve.tateModule_eq_zero_of_forall_frobenius_smul_smul_eq N₀ hpN₀ A hA σ hσ hqp x hx

private theorem w_basis (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Nonempty (Module.Basis (Fin r) ℤ_[p] (TateModule p M)) :=
  TateModule.nonempty_basis_of_card_torsionBy p r hcard

private theorem w_count (N : ℕ) [NeZero N]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
      = n ^ Module.finrank ℤ (ModularCurve.periodLattice N) :=
  ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice N n hn

section Engine

variable {R : Type*} [CommRing R] [IsDomain R]
variable {T : Type*} [AddCommGroup T] [Module R T] [Module.Free R T] [Module.Finite R T]

private theorem exists_ne_zero_forall_exists_apply_eq_smul_of_injective (f : T →ₗ[R] T)
    (hf : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ ∀ z : T, ∃ a : T, f a = d • z := by
  classical
  let b := Module.Free.chooseBasis R T
  let M := LinearMap.toMatrix b b f
  have hM : ∀ t : T, M.mulVec (b.equivFun t) = b.equivFun (f t) := by
    intro t
    simp only [M, b.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f t
  refine ⟨M.det, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv
    have h1 : b.equivFun (f (b.equivFun.symm v)) = 0 := by
      rw [← hM, b.equivFun.apply_symm_apply]
      exact hMv
    have h2 : f (b.equivFun.symm v) = 0 := (map_eq_zero_iff _ b.equivFun.injective).mp h1
    have h3 : b.equivFun.symm v = 0 := hf (by rw [h2, map_zero])
    have h4 := congrArg b.equivFun h3
    rwa [b.equivFun.apply_symm_apply, map_zero] at h4
  · intro z
    refine ⟨b.equivFun.symm (M.adjugate.mulVec (b.equivFun z)), ?_⟩
    apply b.equivFun.injective
    rw [← hM, b.equivFun.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

private theorem exists_ne_zero_apply_eq_smul_of_apply_eq_mul_smul (B : T →ₗ[R] T →ₗ[R] R) (σ : T →ₗ[R] T)
    (c ε : R) (hB : ∀ x : T, (∀ y : T, B x y = 0) → x = 0)
    (hBσ : ∀ x y : T, B (σ x) (σ y) = c * B x y) (hc : c ≠ 0) (hε : ε * ε = 1)
    (x : T) (hx0 : x ≠ 0) (hx : σ x = (ε * c) • x) :
    ∃ y : T, y ≠ 0 ∧ σ y = ε • y := by
  obtain ⟨f, hf⟩ : ∃ f : T →ₗ[R] T, f = ε • σ - LinearMap.id := ⟨_, rfl⟩
  have hfapp : ∀ y : T, f y = ε • σ y - y := by
    intro y
    simp [hf]
  by_cases hinj : Function.Injective f
  · exfalso
    obtain ⟨d, hd, hrange⟩ := exists_ne_zero_forall_exists_apply_eq_smul_of_injective f hinj
    have hkill : ∀ y : T, B x (f y) = 0 := by
      intro y
      have h1 := hBσ x y
      rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
      have h2 : c * (ε * B x (σ y) - B x y) = 0 := by linear_combination h1
      have h3 : ε * B x (σ y) - B x y = 0 := (mul_eq_zero.mp h2).resolve_left hc
      rw [hfapp, map_sub, map_smul, smul_eq_mul]
      exact h3
    apply hx0
    apply hB
    intro z
    obtain ⟨a, ha⟩ := hrange z
    have h4 : B x (f a) = 0 := hkill a
    rw [ha, map_smul, smul_eq_mul] at h4
    exact (mul_eq_zero.mp h4).resolve_left hd
  · rw [injective_iff_map_eq_zero] at hinj
    obtain ⟨y, hy⟩ := not_forall.mp hinj
    obtain ⟨hfy, hy0⟩ := Classical.not_imp.mp hy
    refine ⟨y, hy0, ?_⟩
    have h5 : ε • σ y = y := by
      rw [hfapp] at hfy
      exact sub_eq_zero.mp hfy
    calc σ y = (ε * ε) • σ y := by rw [hε, one_smul]
      _ = ε • (ε • σ y) := by rw [mul_smul]
      _ = ε • y := by rw [h5]

end Engine

private theorem natCard_torsionBy_jZero (N : ℕ) [NeZero N] (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (JZero N) (n : ℤ)) =
      Nat.card (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) := rfl

private theorem natCard_torsionBy_jZero_prime_pow (N₀ : ℕ) [NeZero N₀] (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (JZero N₀) ((ℓ ^ n : ℕ) : ℤ)) =
      (ℓ ^ n) ^ Module.finrank ℤ (periodLattice N₀) := by
  rw [natCard_torsionBy_jZero]
  exact w_count N₀ (ℓ ^ n) (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)

private theorem cyclotomicCharacter_frobenius (q : ℕ) [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) q σ.toRingEquiv : ℤ_[q]ˣ) : ℤ_[q]) = p := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
  have hσe : MulSemiringAction.toRingAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (AlgebraicClosure ℚ) σ =
      σ.toRingEquiv := RingEquiv.ext fun _ => rfl
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [map_natCast]
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero n hq.ne_zero⟩

  let cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod (q ^ n))ˣ :=
    (Units.map (PadicInt.toZModPow n : ℤ_[q] →+* ZMod (q ^ n)).toMonoidHom).comp
      ((cyclotomicCharacter (AlgebraicClosure ℚ) q).comp
        (MulSemiringAction.toRingAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (AlgebraicClosure ℚ)))
  have hcyc : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ (q ^ n) = 1 → τ μ = μ ^ ((cyc τ : ZMod (q ^ n))).val := by
    intro τ μ hμ
    have h := cyclotomicCharacter.spec q
      (MulSemiringAction.toRingAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (AlgebraicClosure ℚ) τ) μ hμ
    exact h
  have h := w_cycloChar (q ^ n) cyc hcyc p hp
    (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm) A hA σ hσ
  have h' : PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) q
      (MulSemiringAction.toRingAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (AlgebraicClosure ℚ) σ) :
        ℤ_[q]ˣ) : ℤ_[q]) = p := by
    have h'' : ((cyc σ : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)) = p := by rw [h, ZMod.coe_unitOfCoprime]
    exact h''
  rw [hσe] at h'
  exact h'

private theorem rep_galois_apply (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : _root_.TateModule q (JZero N)) (n : ℕ) :
    ((_root_.TateModule.rep q (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x :
      _root_.TateModule q (JZero N)) : ℕ → JZero N) n = σ • (x : ℕ → JZero N) n :=
  _root_.TateModule.rep_apply σ x n

private theorem rep_end_apply (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (T : Module.End ℤ (JZero N))
    (x : _root_.TateModule q (JZero N)) (n : ℕ) :
    ((_root_.TateModule.rep q (JZero N) (Module.End ℤ (JZero N)) T x : _root_.TateModule q (JZero N)) :
      ℕ → JZero N) n = T ((x : ℕ → JZero N) n) :=
  _root_.TateModule.rep_apply T x n

private theorem coe_zsmul_apply {q : ℕ} {M : Type} [AddCommGroup M] (c : ℤ) (x : _root_.TateModule q M)
    (n : ℕ) : ((c • x : _root_.TateModule q M) : ℕ → M) n = c • (x : ℕ → M) n := rfl

private theorem smul_zsmul_comm (N : ℕ) [NeZero N] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (k : ℤ) (y : JZero N) : σ • (k • y) = k • σ • y :=
  map_zsmul (DistribSMul.toAddMonoidHom (JZero N) σ) k y

end FrobeniusEigenvalueTateModule

theorem solution
    (N₀ : ℕ) [NeZero N₀] {p : ℕ} [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (x : _root_.TateModule q (JZero N₀))
    (hx : ∀ n : ℕ, σ • (x : ℕ → JZero N₀) n = (ε * p) • (x : ℕ → JZero N₀) n) :
    x = 0 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out

  obtain ⟨b⟩ := FrobeniusEigenvalueTateModule.w_basis q (M := JZero N₀) _
    (FrobeniusEigenvalueTateModule.natCard_torsionBy_jZero_prime_pow N₀ q)
  haveI : Module.Free ℤ_[q] (_root_.TateModule q (JZero N₀)) := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[q] (_root_.TateModule q (JZero N₀)) := Module.Finite.of_basis b

  obtain ⟨B, hBσ, hBl, -⟩ := FrobeniusEigenvalueTateModule.w_pairing q N₀
  have hχ := FrobeniusEigenvalueTateModule.cyclotomicCharacter_frobenius q hp hqp A hA σ hσ
  have hεε : (ε : ℤ_[q]) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  by_contra hx0

  have hxT : _root_.TateModule.rep q (JZero N₀) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x =
      ((ε : ℤ_[q]) * p) • x := by
    have hc : ((ε : ℤ_[q]) * p) = ((ε * p : ℤ) : ℤ_[q]) := by simp only [Int.cast_mul, Int.cast_natCast]
    rw [hc, Int.cast_smul_eq_zsmul ℤ_[q] (ε * p) x]
    refine Subtype.ext (funext fun n => ?_)
    simp only [FrobeniusEigenvalueTateModule.rep_galois_apply, FrobeniusEigenvalueTateModule.coe_zsmul_apply]
    exact hx n
  obtain ⟨y, hy0, hy⟩ :=
    FrobeniusEigenvalueTateModule.exists_ne_zero_apply_eq_smul_of_apply_eq_mul_smul B
      (_root_.TateModule.rep q (JZero N₀) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ) (p : ℤ_[q]) ε hBl
      (fun u v => by rw [hBσ, hχ]) (Nat.cast_ne_zero.mpr hp.ne_zero) hεε x hx0 hxT

  rw [Int.cast_smul_eq_zsmul ℤ_[q] ε y] at hy
  refine hy0 (FrobeniusEigenvalueTateModule.w_frobenius_sq N₀ hpN₀ A hA σ hσ hqp y fun n => ?_)
  have hn : σ • (y : ℕ → JZero N₀) n = ε • (y : ℕ → JZero N₀) n := by
    have h := congrArg (fun v : _root_.TateModule q (JZero N₀) => (v : ℕ → JZero N₀) n) hy
    simp only [FrobeniusEigenvalueTateModule.rep_galois_apply, FrobeniusEigenvalueTateModule.coe_zsmul_apply] at h
    exact h
  have hεε' : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [hn, FrobeniusEigenvalueTateModule.smul_zsmul_comm N₀ σ ε, hn, ← mul_smul, hεε', one_smul]

end S_ModularCurve_tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul
end P2MW
export P2MW.S_ModularCurve_tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul (solution)
