-- Prove2me | solution 1 for ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/71d13513-b8d6-5da8-ad4d-a5f6ebf99162

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_Pic0_exists_weilPairing
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_exists_abelJacobiCard
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one"
p2m_attr_erase "simp" "HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

noncomputable section

open Submodule (torsionBy)

namespace HTWP

variable (p : ℕ) [Fact p.Prime]

def CompatSeq : Subsemiring ((n : ℕ) → ZMod (p ^ n)) where
  carrier := {a | ∀ (k₁ k₂ : ℕ) (h : k₁ ≤ k₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ k₁)) (a k₂) = a k₁}
  mul_mem' {a b} ha hb k₁ k₂ h := by
    show ZMod.castHom _ (ZMod (p ^ k₁)) (a k₂ * b k₂) = a k₁ * b k₁
    rw [map_mul, ha k₁ k₂ h, hb k₁ k₂ h]
  one_mem' k₁ k₂ h := by
    show ZMod.castHom _ (ZMod (p ^ k₁)) 1 = 1
    rw [map_one]
  add_mem' {a b} ha hb k₁ k₂ h := by
    show ZMod.castHom _ (ZMod (p ^ k₁)) (a k₂ + b k₂) = a k₁ + b k₁
    rw [map_add, ha k₁ k₂ h, hb k₁ k₂ h]
  zero_mem' k₁ k₂ h := by
    show ZMod.castHom _ (ZMod (p ^ k₁)) 0 = 0
    rw [map_zero]

def evalC (k : ℕ) : CompatSeq p →+* ZMod (p ^ k) :=
  (Pi.evalRingHom (fun n => ZMod (p ^ n)) k).comp (CompatSeq p).subtype

omit [Fact p.Prime] in
theorem evalC_compat (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ k₁))).comp (evalC p k₂) = evalC p k₁ :=
  RingHom.ext fun a => a.2 k₁ k₂ h

def toPadicInt : CompatSeq p →+* ℤ_[p] := PadicInt.lift (evalC_compat p)

theorem toZModPow_toPadicInt (n : ℕ) (a : CompatSeq p) :
    PadicInt.toZModPow n (toPadicInt p a) = (a : (n : ℕ) → ZMod (p ^ n)) n :=
  congrArg (fun f : CompatSeq p →+* ZMod (p ^ n) => f a) (PadicInt.lift_spec (evalC_compat p) n)

omit [Fact p.Prime] in

theorem compat_of_succ (a : (n : ℕ) → ZMod (p ^ n))
    (h : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (a (n + 1)) = a n) :
    a ∈ CompatSeq p := by
  intro k₁ k₂ hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact ZMod.cast_id _ _
  | succ d ih =>
      have hle : k₁ ≤ k₁ + d := Nat.le_add_right _ _
      have e1 := ih hle
      rw [← h (k₁ + d), ← RingHom.comp_apply, ZMod.castHom_comp] at e1
      exact e1

def mkC (a : (n : ℕ) → ZMod (p ^ n))
    (h : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (a (n + 1)) = a n) :
    CompatSeq p := ⟨a, compat_of_succ p a h⟩

theorem toZModPow_toPadicInt_mkC (a : (n : ℕ) → ZMod (p ^ n))
    (h : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (a (n + 1)) = a n) (n : ℕ) :
    PadicInt.toZModPow n (toPadicInt p (mkC p a h)) = a n :=
  toZModPow_toPadicInt p n _

theorem toZModPow_eq_natCast_appr (n : ℕ) (c : ℤ_[p]) :
    PadicInt.toZModPow n c = ((c.appr n : ℕ) : ZMod (p ^ n)) := rfl

section roots

variable (K : Type*) [Field K] [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)]

omit [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem exists_pow_eq (u : Kˣ) : ∃ v : Kˣ, v ^ p = u := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Fact.out : p.Prime).pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hx
    exact u.ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx]

omit [IsAlgClosed K] in

theorem exists_prim_one : ∃ v : Kˣ, IsPrimitiveRoot v p := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p ^ 1)
  rw [pow_one] at hz
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  refine ⟨Units.mk0 z (hz.ne_zero hp0), ?_⟩
  exact IsPrimitiveRoot.coe_units_iff.mp (by rw [Units.val_mk0]; exact hz)

def ζ : ℕ → Kˣ
  | 0 => 1
  | 1 => (exists_prim_one p K).choose
  | (n + 2) => (exists_pow_eq p K (ζ (n + 1))).choose

theorem ζ_zero : ζ p K 0 = 1 := rfl

theorem ζ_succ_pow (n : ℕ) : ζ p K (n + 1) ^ p = ζ p K n := by
  cases n with
  | zero => exact (exists_prim_one p K).choose_spec.pow_eq_one
  | succ n => exact (exists_pow_eq p K (ζ p K (n + 1))).choose_spec

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem isPrimitiveRoot_of_pow_eq {x y : Kˣ} {n : ℕ} (hy : IsPrimitiveRoot y (p ^ (n + 1)))
    (hx : x ^ p = y) : IsPrimitiveRoot x (p ^ (n + 2)) := by
  have hp := (Fact.out : p.Prime)
  have hx1 : x ^ p ^ (n + 2) = 1 := by
    rw [pow_succ' p (n + 1), pow_mul, hx]; exact hy.pow_eq_one
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx1)
  have hoy : orderOf y = p ^ (n + 1) := hy.eq_orderOf.symm
  have hdvd : p ^ (n + 1) ∣ p ^ j := by
    rw [← hoy, ← hjeq, ← hx]; exact orderOf_pow_dvd p
  have hj' : n + 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  rcases Nat.lt_or_ge j (n + 2) with hlt | hge
  · have hjn : j = n + 1 := by omega
    exfalso
    have h1 : x ^ p ^ (n + 1) = 1 := by rw [← hjn, ← hjeq]; exact pow_orderOf_eq_one x
    have h2 : y ^ p ^ n = 1 := by
      rw [← hx, ← pow_mul, ← pow_succ']; exact h1
    have h3 := hy.dvd_of_pow_eq_one _ h2
    have : p ^ (n + 1) ≤ p ^ n := Nat.le_of_dvd (pow_pos hp.pos n) h3
    exact absurd this (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n)))
  · have hjn : j = n + 2 := le_antisymm hj hge
    rw [hjn] at hjeq
    rw [← hjeq]
    exact IsPrimitiveRoot.orderOf x

theorem isPrimitiveRoot_ζ (n : ℕ) : IsPrimitiveRoot (ζ p K n) (p ^ n) := by
  induction n with
  | zero => rw [ζ_zero, pow_zero]; exact IsPrimitiveRoot.one
  | succ n ih =>
      cases n with
      | zero => rw [zero_add, pow_one]; exact (exists_prim_one p K).choose_spec
      | succ n => exact isPrimitiveRoot_of_pow_eq p K ih (ζ_succ_pow p K (n + 1))

theorem ζ_pow_pow (n : ℕ) : ζ p K n ^ p ^ n = 1 := (isPrimitiveRoot_ζ p K n).pow_eq_one

variable {K}

theorem mem_zpowers_ζ {n : ℕ} {u : Kˣ} (hu : u ^ p ^ n = 1) : u ∈ Subgroup.zpowers (ζ p K n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rw [(isPrimitiveRoot_ζ p K n).zpowers_eq]
  exact (mem_rootsOfUnity _ _).2 hu

def toZPowers (n : ℕ) (u : Kˣ) (hu : u ^ p ^ n = 1) : Additive (Subgroup.zpowers (ζ p K n)) :=
  Additive.ofMul ⟨u, mem_zpowers_ζ p hu⟩

def dlog (n : ℕ) (u : Kˣ) (hu : u ^ p ^ n = 1) : ZMod (p ^ n) :=
  (isPrimitiveRoot_ζ p K n).zmodEquivZPowers.symm (toZPowers p n u hu)

theorem dlog_eq_of_pow_eq (n : ℕ) (u : Kˣ) (hu : u ^ p ^ n = 1) (k : ℕ) (hk : ζ p K n ^ k = u) :
    dlog p n u hu = k := by
  have : toZPowers p n u hu = Additive.ofMul ⟨ζ p K n ^ k, k, rfl⟩ :=
    congrArg Additive.ofMul (Subtype.ext hk.symm)
  unfold dlog
  rw [this]
  exact (isPrimitiveRoot_ζ p K n).zmodEquivZPowers_symm_apply_pow k

theorem dlog_spec (n : ℕ) (u : Kˣ) (hu : u ^ p ^ n = 1) : ζ p K n ^ (dlog p n u hu).val = u := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have h := isPrimitiveRoot_ζ p K n
  have e1 : h.zmodEquivZPowers (((dlog p n u hu).val : ℕ) : ZMod (p ^ n)) = toZPowers p n u hu := by
    rw [ZMod.natCast_zmod_val]; exact AddEquiv.apply_symm_apply _ _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at e1
  exact congrArg
    (fun z : Additive (Subgroup.zpowers (ζ p K n)) => ((Additive.toMul z : Subgroup.zpowers _) : Kˣ)) e1

theorem dlog_mul (n : ℕ) (u v : Kˣ) (hu : u ^ p ^ n = 1) (hv : v ^ p ^ n = 1)
    (huv : (u * v) ^ p ^ n = 1) : dlog p n (u * v) huv = dlog p n u hu + dlog p n v hv := by
  unfold dlog
  rw [← map_add]
  rfl

theorem dlog_pow (n : ℕ) (u : Kˣ) (hu : u ^ p ^ n = 1) (k : ℕ) (huk : (u ^ k) ^ p ^ n = 1) :
    dlog p n (u ^ k) huk = (k : ZMod (p ^ n)) * dlog p n u hu := by
  have h : ζ p K n ^ (k * (dlog p n u hu).val) = u ^ k := by
    rw [mul_comm, pow_mul, dlog_spec p n u hu]
  rw [dlog_eq_of_pow_eq p n _ huk _ h, Nat.cast_mul, ZMod.natCast_zmod_val]

theorem castHom_dlog_succ (n : ℕ) (v : Kˣ) (hv : v ^ p ^ (n + 1) = 1) (hvp : (v ^ p) ^ p ^ n = 1) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (dlog p (n + 1) v hv) =
      dlog p n (v ^ p) hvp := by
  set k := (dlog p (n + 1) v hv).val with hk
  have h1 : ζ p K (n + 1) ^ k = v := dlog_spec p (n + 1) v hv
  have h2 : ζ p K n ^ k = v ^ p := by
    rw [← ζ_succ_pow, ← pow_mul, mul_comm, pow_mul, h1]
  rw [dlog_eq_of_pow_eq p n _ hvp k h2, ← ZMod.natCast_zmod_val (dlog p (n + 1) v hv), map_natCast]

theorem dlog_map (n : ℕ) (τ : K ≃+* K) (u : Kˣ) (hu : u ^ p ^ n = 1)
    (hτu : (Units.map (τ : K →* K) u) ^ p ^ n = 1) :
    dlog p n (Units.map (τ : K →* K) u) hτu =
      PadicInt.toZModPow n ((cyclotomicCharacter K p τ : ℤ_[p]ˣ) : ℤ_[p]) * dlog p n u hu := by
  set c := PadicInt.toZModPow n ((cyclotomicCharacter K p τ : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hζK : ((ζ p K n : Kˣ) : K) ^ p ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ζ_pow_pow, Units.val_one]
  have hspec : τ ((ζ p K n : Kˣ) : K) = ((ζ p K n : Kˣ) : K) ^ c.val :=
    cyclotomicCharacter.spec p τ _ hζK
  have hk := dlog_spec p n u hu

  have h1 : ζ p K n ^ (c.val * (dlog p n u hu).val) = Units.map (τ : K →* K) u := by
    apply Units.ext
    rw [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, pow_mul, ← hspec, ← map_pow,
      ← Units.val_pow_eq_pow_val, hk]
  rw [dlog_eq_of_pow_eq p n _ hτu _ h1, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

end roots

section pairing

variable {K : Type*} [Field K] [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)]
variable {A : Type} [AddCommGroup A]

def P1 (e : ℕ → A → A → K) : Prop :=
  ∀ (n : ℕ) (x y : A), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1

def P2 (e : ℕ → A → A → K) : Prop :=
  ∀ (n : ℕ) (x x' y : A), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
    e n (x + x') y = e n x y * e n x' y

def P3 (e : ℕ → A → A → K) : Prop :=
  ∀ (n : ℕ) (x y y' : A), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
    e n x (y + y') = e n x y * e n x y'

def P4 (e : ℕ → A → A → K) : Prop :=
  ∀ (n : ℕ) (x : A), 0 < n → (n : ℤ) • x = 0 → (∀ y : A, (n : ℤ) • y = 0 → e n x y = 1) → x = 0

def P5 (e : ℕ → A → A → K) : Prop :=
  ∀ (n : ℕ) (y : A), 0 < n → (n : ℤ) • y = 0 → (∀ x : A, (n : ℤ) • x = 0 → e n x y = 1) → y = 0

def P6 (e : ℕ → A → A → K) : Prop :=
  ∀ (n m : ℕ) (x y : A), 0 < n → 0 < m →
    ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
    e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m

variable (e : ℕ → A → A → K)

local notation "T" => TateModule p A

theorem ppos (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem e_zero_left (h1 : P1 e) (h2 : P2 e) {n : ℕ} (hn : 0 < n) (y : A) (hy : (n : ℤ) • y = 0) :
    e n 0 y = 1 := by
  have h := h2 n 0 0 y hn (smul_zero _) (smul_zero _) hy
  rw [add_zero] at h
  have hne : e n 0 y ≠ 0 := by
    intro h0
    have := h1 n 0 y hn (smul_zero _) hy
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact (mul_eq_left₀ hne).mp h.symm

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem e_nsmul_left (h1 : P1 e) (h2 : P2 e) {n : ℕ} (hn : 0 < n) (k : ℕ) (x y : A)
    (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0) : e n (k • x) y = e n x y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact e_zero_left e h1 h2 hn y hy
  | succ k ih =>
      have hkx : (n : ℤ) • (k • x) = 0 := by rw [smul_comm, hx, smul_zero]
      rw [succ_nsmul, h2 n _ _ _ hn hkx hx hy, ih, pow_succ]

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem e_zero_right (h1 : P1 e) (h3 : P3 e) {n : ℕ} (hn : 0 < n) (x : A) (hx : (n : ℤ) • x = 0) :
    e n x 0 = 1 := by
  have h := h3 n x 0 0 hn hx (smul_zero _) (smul_zero _)
  rw [add_zero] at h
  have hne : e n x 0 ≠ 0 := by
    intro h0
    have := h1 n x 0 hn hx (smul_zero _)
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact (mul_eq_left₀ hne).mp h.symm

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem e_nsmul_right (h1 : P1 e) (h3 : P3 e) {n : ℕ} (hn : 0 < n) (k : ℕ) (x y : A)
    (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0) : e n x (k • y) = e n x y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact e_zero_right e h1 h3 hn x hx
  | succ k ih =>
      have hky : (n : ℤ) • (k • y) = 0 := by rw [smul_comm, hy, smul_zero]
      rw [succ_nsmul, h3 n _ _ _ hn hx hky hy, ih, pow_succ]

section withH1

variable (h1 : P1 e)
include h1

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in
theorem e_ne_zero (n : ℕ) (x y : T) : e (p ^ n) ((x : ℕ → A) n) ((y : ℕ → A) n) ≠ 0 := by
  intro h0
  have := h1 (p ^ n) ((x : ℕ → A) n) ((y : ℕ → A) n) (ppos p n) (TateModule.torsion x n)
    (TateModule.torsion y n)
  rw [h0, zero_pow (ppos p n).ne'] at this
  exact zero_ne_one this

def uu (n : ℕ) (x y : T) : Kˣ :=
  Units.mk0 (e (p ^ n) ((x : ℕ → A) n) ((y : ℕ → A) n)) (e_ne_zero p e h1 n x y)

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in
theorem coe_uu (n : ℕ) (x y : T) :
    ((uu p e h1 n x y : Kˣ) : K) = e (p ^ n) ((x : ℕ → A) n) ((y : ℕ → A) n) := rfl

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in
theorem uu_pow (n : ℕ) (x y : T) : uu p e h1 n x y ^ p ^ n = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, coe_uu, Units.val_one]
    exact h1 _ _ _ (ppos p n) (TateModule.torsion x n) (TateModule.torsion y n))

omit [IsAlgClosed K] [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] in

theorem uu_succ_pow (h6 : P6 e) (n : ℕ) (x y : T) : uu p e h1 (n + 1) x y ^ p = uu p e h1 n x y := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_uu, coe_uu, ← TateModule.compat x n, ← TateModule.compat y n]
  have hx : ((p ^ n * p : ℕ) : ℤ) • (x : ℕ → A) (n + 1) = 0 := by
    rw [← pow_succ]; exact TateModule.torsion x _
  have hy : ((p ^ n * p : ℕ) : ℤ) • (y : ℕ → A) (n + 1) = 0 := by
    rw [← pow_succ]; exact TateModule.torsion y _
  rw [h6 (p ^ n) p _ _ (ppos p n) (Fact.out : p.Prime).pos hx hy, ← pow_succ]

def aa (n : ℕ) (x y : T) : ZMod (p ^ n) := dlog p n (uu p e h1 n x y) (uu_pow p e h1 n x y)

theorem aa_compat (h6 : P6 e) (x y : T) (n : ℕ) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (aa p e h1 (n + 1) x y) =
      aa p e h1 n x y := by
  have hvp : (uu p e h1 (n + 1) x y ^ p) ^ p ^ n = 1 := by
    rw [uu_succ_pow p e h1 h6]; exact uu_pow p e h1 n x y
  unfold aa
  rw [castHom_dlog_succ p n _ _ hvp]
  congr 1
  exact uu_succ_pow p e h1 h6 n x y

def Bfun (h6 : P6 e) (x y : T) : ℤ_[p] :=
  toPadicInt p (mkC p (fun n => aa p e h1 n x y) (aa_compat p e h1 h6 x y))

theorem toZModPow_Bfun (h6 : P6 e) (n : ℕ) (x y : T) :
    PadicInt.toZModPow n (Bfun p e h1 h6 x y) = aa p e h1 n x y :=
  toZModPow_toPadicInt_mkC p _ _ n

theorem aa_add_left (h2 : P2 e) (n : ℕ) (x x' y : T) :
    aa p e h1 n (x + x') y = aa p e h1 n x y + aa p e h1 n x' y := by
  unfold aa
  rw [← dlog_mul p n _ _ (uu_pow p e h1 n x y) (uu_pow p e h1 n x' y)
    (by rw [mul_pow, uu_pow, uu_pow, one_mul])]
  congr 1
  apply Units.ext
  rw [coe_uu, Units.val_mul, coe_uu, coe_uu]
  exact h2 _ _ _ _ (ppos p n) (TateModule.torsion x n) (TateModule.torsion x' n)
    (TateModule.torsion y n)

theorem aa_add_right (h3 : P3 e) (n : ℕ) (x y y' : T) :
    aa p e h1 n x (y + y') = aa p e h1 n x y + aa p e h1 n x y' := by
  unfold aa
  rw [← dlog_mul p n _ _ (uu_pow p e h1 n x y) (uu_pow p e h1 n x y')
    (by rw [mul_pow, uu_pow, uu_pow, one_mul])]
  congr 1
  apply Units.ext
  rw [coe_uu, Units.val_mul, coe_uu, coe_uu]
  exact h3 _ _ _ _ (ppos p n) (TateModule.torsion x n) (TateModule.torsion y n)
    (TateModule.torsion y' n)

theorem aa_smul_left (h2 : P2 e) (n : ℕ) (c : ℤ_[p]) (x y : T) :
    aa p e h1 n (c • x) y = PadicInt.toZModPow n c * aa p e h1 n x y := by
  unfold aa
  rw [toZModPow_eq_natCast_appr, ← dlog_pow p n _ (uu_pow p e h1 n x y) (c.appr n)
    (by rw [← pow_mul, mul_comm, pow_mul, uu_pow, one_pow])]
  congr 1
  apply Units.ext
  rw [coe_uu, Units.val_pow_eq_pow_val, coe_uu, TateModule.smul_apply, natCast_zsmul]
  exact e_nsmul_left e h1 h2 (ppos p n) _ _ _ (TateModule.torsion x n) (TateModule.torsion y n)

theorem aa_smul_right (h3 : P3 e) (n : ℕ) (c : ℤ_[p]) (x y : T) :
    aa p e h1 n x (c • y) = PadicInt.toZModPow n c * aa p e h1 n x y := by
  unfold aa
  rw [toZModPow_eq_natCast_appr, ← dlog_pow p n _ (uu_pow p e h1 n x y) (c.appr n)
    (by rw [← pow_mul, mul_comm, pow_mul, uu_pow, one_pow])]
  congr 1
  apply Units.ext
  rw [coe_uu, Units.val_pow_eq_pow_val, coe_uu, TateModule.smul_apply, natCast_zsmul]
  exact e_nsmul_right e h1 h3 (ppos p n) _ _ _ (TateModule.torsion x n) (TateModule.torsion y n)

def B (h2 : P2 e) (h3 : P3 e) (h6 : P6 e) : T →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] ℤ_[p] :=
  LinearMap.mk₂ ℤ_[p] (Bfun p e h1 h6)
    (fun x x' y => PadicInt.ext_of_toZModPow.mp fun n => by
      rw [map_add, toZModPow_Bfun, toZModPow_Bfun, toZModPow_Bfun, aa_add_left p e h1 h2])
    (fun c x y => PadicInt.ext_of_toZModPow.mp fun n => by
      rw [smul_eq_mul, map_mul, toZModPow_Bfun, toZModPow_Bfun, aa_smul_left p e h1 h2])
    (fun x y y' => PadicInt.ext_of_toZModPow.mp fun n => by
      rw [map_add, toZModPow_Bfun, toZModPow_Bfun, toZModPow_Bfun, aa_add_right p e h1 h3])
    (fun c x y => PadicInt.ext_of_toZModPow.mp fun n => by
      rw [smul_eq_mul, map_mul, toZModPow_Bfun, toZModPow_Bfun, aa_smul_right p e h1 h3])

theorem toZModPow_B (h2 : P2 e) (h3 : P3 e) (h6 : P6 e) (n : ℕ) (x y : T) :
    PadicInt.toZModPow n (B p e h1 h2 h3 h6 x y) = aa p e h1 n x y :=
  toZModPow_Bfun p e h1 h6 n x y

theorem B_rep (h2 : P2 e) (h3 : P3 e) (h6 : P6 e) {G : Type} [Monoid G] [DistribMulAction G A]
    (τ : G → (K ≃+* K))
    (hgal : ∀ (n : ℕ) (σ : G) (x y : A), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (σ • x) (σ • y) = τ σ (e n x y))
    (σ : G) (x y : T) :
    B p e h1 h2 h3 h6 (TateModule.rep p A G σ x) (TateModule.rep p A G σ y) =
      ((cyclotomicCharacter K p (τ σ) : ℤ_[p]ˣ) : ℤ_[p]) * B p e h1 h2 h3 h6 x y := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [map_mul, toZModPow_B, toZModPow_B]
  have hmap : (Units.map ((τ σ : K ≃+* K) : K →* K) (uu p e h1 n x y)) ^ p ^ n = 1 := by
    rw [← map_pow, uu_pow, map_one]
  unfold aa
  rw [← dlog_map p n (τ σ) _ (uu_pow p e h1 n x y) hmap]
  congr 1
  apply Units.ext
  rw [coe_uu, Units.coe_map, MonoidHom.coe_coe, coe_uu]
  exact hgal _ σ _ _ (ppos p n) (TateModule.torsion x n) (TateModule.torsion y n)

theorem e_eq_one_of_aa_eq_zero (n : ℕ) (x y : T) (h : aa p e h1 n x y = 0) :
    e (p ^ n) ((x : ℕ → A) n) ((y : ℕ → A) n) = 1 := by
  have hs := dlog_spec p n (uu p e h1 n x y) (uu_pow p e h1 n x y)
  change ζ p K n ^ (aa p e h1 n x y).val = uu p e h1 n x y at hs
  rw [h, ZMod.val_zero, pow_zero] at hs
  have := congrArg Units.val hs
  rw [Units.val_one, coe_uu] at this
  exact this.symm

theorem B_right (h2 : P2 e) (h3 : P3 e) (h6 : P6 e) (h5 : P5 e)
    (hlift : ∀ (n : ℕ) (z : A), ((p ^ n : ℕ) : ℤ) • z = 0 → ∃ x : T, (x : ℕ → A) n = z)
    (y : T) (hy : ∀ x : T, B p e h1 h2 h3 h6 x y = 0) : y = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  refine h5 (p ^ n) _ (ppos p n) (TateModule.torsion y n) fun z hz => ?_
  obtain ⟨x, rfl⟩ := hlift n z hz
  refine e_eq_one_of_aa_eq_zero p e h1 n x y ?_
  rw [← toZModPow_B p e h1 h2 h3 h6, hy x, map_zero]

theorem B_left (h2 : P2 e) (h3 : P3 e) (h6 : P6 e) (h4 : P4 e)
    (hlift : ∀ (n : ℕ) (z : A), ((p ^ n : ℕ) : ℤ) • z = 0 → ∃ x : T, (x : ℕ → A) n = z)
    (x : T) (hx : ∀ y : T, B p e h1 h2 h3 h6 x y = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  refine h4 (p ^ n) _ (ppos p n) (TateModule.torsion x n) fun z hz => ?_
  obtain ⟨y, rfl⟩ := hlift n z hz
  refine e_eq_one_of_aa_eq_zero p e h1 n x y ?_
  rw [← toZModPow_B p e h1 h2 h3 h6, hx y, map_zero]

end withH1

end pairing

section lifting

variable {A : Type} [AddCommGroup A] {d : ℕ}
  (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ A ((p ^ n : ℕ) : ℤ)) = p ^ (d * n))

include hcard

theorem finite_torsionBy' (n : ℕ) : Finite (torsionBy ℤ A ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by rw [hcard n]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem mulP_surjective' (n : ℕ) : Function.Surjective (TateModule.mulP p A n) := by
  haveI := finite_torsionBy' p hcard (n + 1)
  haveI := finite_torsionBy' p hcard n
  have hker : Nat.card (TateModule.mulP p A n).ker = p ^ d := by
    rw [Nat.card_congr (TateModule.kerMulPEquiv p A n), hcard 1, mul_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (TateModule.mulP p A n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (TateModule.mulP p A n)).toEquiv,
    hker] at h
  have hrange : Nat.card (TateModule.mulP p A n).range = Nat.card (torsionBy ℤ A ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos d) ?_
    rw [← h, ← pow_add, mul_add, mul_one]
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem exists_apply_eq (n : ℕ) (z : A) (hz : ((p ^ n : ℕ) : ℤ) • z = 0) :
    ∃ x : TateModule p A, (x : ℕ → A) n = z := by
  choose next hnext using fun k (m : torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) => mulP_surjective' p hcard k m
  have hz' : z ∈ torsionBy ℤ A ((p ^ n : ℕ) : ℤ) := (Submodule.mem_torsionBy_iff _ _).2 hz
  refine ⟨⟨TateModule.liftFun next n ⟨z, hz'⟩,
    TateModule.liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨z, hz'⟩⟩, ?_⟩
  change TateModule.liftFun next n ⟨z, hz'⟩ n = z
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self n)]
  rfl

end lifting

end HTWP

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] :
    ∃ B : TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]]
        ℤ_[p],
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : TateModule p (ModularCurve.JZero M)),
        B (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
            (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              y) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B x y) ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      (∀ y, (∀ x, B x y = 0) → y = 0) := by
  classical
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar M

  have hW := AlgebraicCurve.Pic0.exists_weilPairing.{0, 0, 0} (AlgebraicClosure ℚ)
    (ModularCurve.modularFunctionFieldBar M)
    (ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar M)
  rcases hW with ⟨e, h1, h2, h3, h4, h5, h6, h7, -⟩

  have hAJ := ModularCurve.JZero.exists_abelJacobiCard M
  rcases hAJ with ⟨g, hg⟩
  have hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ (ModularCurve.JZero M) ((p ^ n : ℕ) : ℤ)) =
      p ^ (2 * g * n) := fun n => hg p n
  have hlift := HTWP.exists_apply_eq p hcard

  have hgal : ∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x y : ModularCurve.JZero M), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (σ • x) (σ • y) = σ.toRingEquiv (e n x y) :=
    fun n σ x y hn hx hy =>
      h7 n (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull M) σ) x y hn hx hy
  refine ⟨HTWP.B p e h1 h2 h3 h6, fun σ x y => ?_, HTWP.B_left p e h1 h2 h3 h6 h4 hlift,
    HTWP.B_right p e h1 h2 h3 h6 h5 hlift⟩
  exact HTWP.B_rep p e h1 h2 h3 h6 (fun σ => σ.toRingEquiv) hgal σ x y

end
end S_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
end P2MW
export P2MW.S_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul (solution)
