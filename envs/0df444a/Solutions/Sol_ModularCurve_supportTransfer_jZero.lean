-- Prove2me | solution 1 for ModularCurve.supportTransfer_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a92cc46a-b3de-5c65-b70b-c627372b46c7

import Mathlib
import Definitions.Def_FreyPackage_MazurAttachmentApparatus
import Definitions.Def_ModularCurve_SupportTransfer
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_heckeRelations_jZero
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_DeligneSerre_exists_minimalPrime_le
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo
import Theorems.Thm_ResidualGaloisRep_isAttachedTo_iff_trace_det
import Theorems.Thm_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Theorems.Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_supportTransfer_jZero
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree"
p2m_attr_erase "instance" "GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.cuspCount_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateModule.smul_apply"
p2m_attr_erase "simp" "TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left"
p2m_attr_erase "simp" "ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open ModularCurve CuspForm MvPolynomial
open scoped CongruenceSubgroup WeierstrassCurve.Affine

noncomputable section

namespace P2mWs11Rb

theorem exists_numberField_ker_restrictNormalHom_le
    (L₁ L₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₁] [FiniteDimensional ℚ L₂] :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker →
        (∀ x ∈ L₁, σ x = x) ∧ (∀ x ∈ L₂, σ x = x) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    normal_iff.mpr fun x =>
      ⟨(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral, IsAlgClosed.splits _⟩
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := L₁ ⊔ L₂
  haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup L₁ L₂
  let Fi : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)
  haveI hfd : FiniteDimensional ℚ Fi := normalClosure.is_finiteDimensional ℚ E (AlgebraicClosure ℚ)
  haveI hn : Normal ℚ Fi := normalClosure.normal ℚ E (AlgebraicClosure ℚ)
  haveI : Algebra.IsSeparable ℚ Fi := Algebra.IsSeparable.of_integral ℚ Fi
  haveI hg : IsGalois ℚ Fi := IsGalois.mk
  have hE : E ≤ Fi := IntermediateField.le_normalClosure E
  have hinst : (Fi.algebra : Algebra ℚ Fi) = (DivisionRing.toRatAlgebra : Algebra ℚ Fi) :=
    Subsingleton.elim _ _
  refine ⟨Fi, inferInstance, ?_, ?_, inferInstance, ?_, ?_⟩
  · exact { to_charZero := inferInstance, to_finiteDimensional := hinst ▸ hfd }
  · exact hinst ▸ hg
  · exact hinst ▸ (inferInstance : IsScalarTower ℚ Fi (AlgebraicClosure ℚ))
  · intro σ hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Fi) σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have hfix : ∀ x : AlgebraicClosure ℚ, x ∈ Fi → σ x = x := by
      intro x hx
      have h2 := AlgEquiv.restrictNormal_commutes σ Fi ⟨x, hx⟩
      change (AlgEquiv.restrictNormalHom Fi σ) = 1 at h1
      rw [show σ.restrictNormal Fi = AlgEquiv.restrictNormalHom Fi σ from rfl, h1] at h2
      simpa using h2.symm
    exact ⟨fun x hx => hfix x (hE ((le_sup_left : L₁ ≤ E) hx)),
      fun x hx => hfix x (hE ((le_sup_right : L₂ ≤ E) hx))⟩

end P2mWs11Rb

open P2mWs11Rb in
theorem solution (N q p : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hp : p.Prime) (hqN : ¬ q ∣ N)
    (W : WeierstrassCurve ℤ) (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal) (hpmem : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪)
    (hgood : FreyPackage.IdealGoodPrimeCurveCongruence p (N * q) W 𝔪)
    (hinN : ModularCurve.HeckeInputsAll N) (hcommN : ModularCurve.HeckeOperatorsCommuteBar N)
    (S : Finset Nat.Primes) (hS : ∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q) :
    letI := ModularCurve.heckeModuleBar N
    ModularCurve.SupportTransfer N W p S 𝔪 (ModularCurve.JZero N) := by
  classical
  letI := ModularCurve.heckeModuleBar N
  rintro ⟨y, hy0, hnat, hgen⟩

  let ev : HeckeAlg →ₐ[ℤ] CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N} :=
    MvPolynomial.aeval (R := ℤ)
      (fun ℓ : Nat.Primes => if h : ¬ (ℓ : ℕ) ∣ N
        then (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) ℓ.prop h h : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N})
        else 0)
  let Asupp : Subalgebra ℤ HeckeAlg := MvPolynomial.supported ℤ {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N}
  have hevX : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      ev (heckeGen ⟨ℓ, hℓ⟩) = CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hℓ hℓN hℓN := by
    intro ℓ hℓ hℓN
    show MvPolynomial.aeval _ (MvPolynomial.X _) = _
    rw [MvPolynomial.aeval_X]
    exact dif_pos hℓN

  have hsurj : ∀ t : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}, ∃ P ∈ Asupp, ev P = t := by
    rintro ⟨x, hx⟩
    refine Algebra.adjoin_induction
      (p := fun x hx => ∃ P ∈ Asupp, ev P = ⟨x, hx⟩) ?_ ?_ ?_ ?_ hx
    · rintro x (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q', hq'N, hq', hq'S, rfl⟩)
      · refine ⟨heckeGen ⟨ℓ, hℓ⟩, ?_, ?_⟩
        · exact (MvPolynomial.X_mem_supported).mpr hℓN
        · rw [hevX hℓ hℓN]; rfl
      · exact absurd hq'N hq'S
    · intro r
      refine ⟨algebraMap ℤ HeckeAlg r, Subalgebra.algebraMap_mem _ r, ?_⟩
      rw [AlgHom.commutes]; rfl
    · rintro x₁ x₂ hx₁ hx₂ ⟨P₁, hP₁, he₁⟩ ⟨P₂, hP₂, he₂⟩
      exact ⟨P₁ + P₂, Subalgebra.add_mem _ hP₁ hP₂, by rw [map_add, he₁, he₂]; rfl⟩
    · rintro x₁ x₂ hx₁ hx₂ ⟨P₁, hP₁, he₁⟩ ⟨P₂, hP₂, he₂⟩
      exact ⟨P₁ * P₂, Subalgebra.mul_mem _ hP₁ hP₂, by rw [map_mul, he₁, he₂]; rfl⟩

  have hpy : (MvPolynomial.C (p : ℤ) : HeckeAlg) • y = 0 := by
    have : (MvPolynomial.C (p : ℤ) : HeckeAlg) = ((p : ℕ) : HeckeAlg) := by simp
    rw [this]; exact hnat p hpmem
  have hgy : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓq : ℓ ≠ q) (hg : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p),
      (heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ)) • y = 0 := by
    intro ℓ hℓ hℓN hℓq hg hℓp
    have hℓNq : ¬ ℓ ∣ N * q := by
      intro hd
      rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
      · exact hℓN h
      · exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp h)
    have hℓS : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S := fun h => hℓNq (hS _ h)
    exact hgen ⟨ℓ, hℓ⟩ hℓS _ (hgood ℓ hℓ hg hℓNq hℓp)

  let gens₀ : Set (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) :=
    insert ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N})
      {x | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), W.IsGoodPrimeFor ℓ ∧ ℓ ≠ p ∧ ℓ ≠ q ∧ x = exitGen N W ℓ hℓ hℓN}
  let I₀ : Ideal (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) := Ideal.span gens₀
  have hgood₀ : ∀ t ∈ I₀, ∃ P ∈ Asupp, P • y = 0 ∧ ev P = t := by
    intro t ht
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
    · rintro x (rfl | ⟨ℓ, hℓ, hℓN, hg, hℓp, hℓq, rfl⟩)
      · refine ⟨MvPolynomial.C (p : ℤ), Subalgebra.algebraMap_mem _ (p : ℤ), hpy, ?_⟩
        show MvPolynomial.aeval _ (MvPolynomial.C (p : ℤ)) = _
        rw [MvPolynomial.aeval_C]; simp
      · refine ⟨heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ),
          Subalgebra.sub_mem _ ((MvPolynomial.X_mem_supported).mpr hℓN) (Subalgebra.algebraMap_mem _ _),
          hgy hℓ hℓN hℓq hg hℓp, ?_⟩
        rw [map_sub, hevX hℓ hℓN]
        show _ - MvPolynomial.aeval _ (MvPolynomial.C _) = _
        rw [MvPolynomial.aeval_C]
        simp [exitGen]
    · exact ⟨0, Subalgebra.zero_mem _, zero_smul HeckeAlg y, map_zero _⟩
    · rintro x₁ x₂ - - ⟨P₁, hP₁, hy₁, he₁⟩ ⟨P₂, hP₂, hy₂, he₂⟩
      exact ⟨P₁ + P₂, Subalgebra.add_mem _ hP₁ hP₂, by rw [add_smul, hy₁, hy₂, add_zero], by rw [map_add, he₁, he₂]⟩
    · rintro c x - ⟨P, hP, hyP, heP⟩
      obtain ⟨Q, hQ, heQ⟩ := hsurj c
      exact ⟨Q * P, Subalgebra.mul_mem _ hQ hP, by rw [mul_smul, hyP]; exact smul_zero (A := JZero N) Q, by rw [map_mul, heQ, heP, smul_eq_mul]⟩
  have hI₀ : I₀ ≠ ⊤ := by
    intro htop
    obtain ⟨P, hP, hyP, heP⟩ := hgood₀ 1 (htop ▸ Submodule.mem_top)
    have hu : (1 - P : HeckeAlg) • y = 0 :=
      ModularCurve.heckeRelations_jZero N hinN hcommN (1 - P) (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hP)
        (by rw [map_sub, map_one]; exact sub_eq_zero.mpr heP.symm) y
    apply hy0
    calc y = (1 : HeckeAlg) • y := (one_smul _ _).symm
      _ = (1 - P + P : HeckeAlg) • y := by rw [sub_add_cancel]
      _ = 0 := by rw [add_smul, hu, hyP, add_zero]

  obtain ⟨𝔪₁, h𝔪₁max, hI₀𝔪₁⟩ := Ideal.exists_le_maximal I₀ hI₀
  have hp𝔪₁ : ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ 𝔪₁ :=
    hI₀𝔪₁ (Ideal.subset_span (Set.mem_insert _ _))
  have hgen𝔪₁ : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), W.IsGoodPrimeFor ℓ → ℓ ≠ p → ℓ ≠ q →
      exitGen N W ℓ hℓ hℓN ∈ 𝔪₁ :=
    fun hℓ hℓN hg hℓp hℓq => hI₀𝔪₁ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨_, hℓ, hℓN, hg, hℓp, hℓq, rfl⟩))
  suffices hq𝔪₁ : W.IsGoodPrimeFor q → q ≠ p → exitGen N W q hq hqN ∈ 𝔪₁ by
    intro htop
    apply h𝔪₁max.ne_top
    rw [eq_top_iff, ← htop]
    refine Ideal.span_le.mpr ?_
    rintro x (rfl | ⟨ℓ, hℓ, hℓN, hg, hℓp, rfl⟩)
    · exact hp𝔪₁
    · by_cases hℓq : ℓ = q
      · subst hℓq; exact hq𝔪₁ hg hℓp
      · exact hgen𝔪₁ hℓ hℓN hg hℓp hℓq
  intro hqgood hqp

  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) := CuspForm.moduleFinite_heckeAlgebra_two N _
  haveI : Module.IsTorsionFree ℤ (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) := inferInstance
  haveI hint : Algebra.IsIntegral ℤ (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) := Algebra.IsIntegral.of_finite ℤ _
  obtain ⟨𝔭, h𝔭min, h𝔭le, -⟩ := DeligneSerre.exists_minimalPrime_le 𝔪₁ h𝔪₁max.isPrime
  obtain ⟨f, hf, hann⟩ :=
    CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime {n : ℕ | n ∣ N} 𝔭 h𝔭min.1.1
  obtain ⟨χ₀, hχ₀, -, -⟩ := hf.exists_ringHom_heckeAlgebra {n : ℕ | n ∣ N}
  have hχint : ∀ t : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}, χ₀ t ∈ integralClosure ℤ ℂ := fun t =>
    (hint.isIntegral t).map χ₀.toIntAlgHom
  let χ : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N} →+* integralClosure ℤ ℂ := χ₀.codRestrict (integralClosure ℤ ℂ) hχint
  have hχ : ∀ t : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N},
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = ((χ t : integralClosure ℤ ℂ) : ℂ) • f :=
    fun t => hχ₀ t
  have hkerχ : RingHom.ker χ ≤ 𝔪₁ := by
    intro t ht
    refine h𝔭le (hann t ?_)
    rw [hχ t, show ((χ t : integralClosure ℤ ℂ) : ℂ) = 0 by rw [RingHom.mem_ker.mp ht]; rfl, zero_smul]
  letI : Algebra (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) (integralClosure ℤ ℂ) := χ.toAlgebra
  haveI : IsScalarTower ℤ (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) (integralClosure ℤ ℂ) := by
    refine IsScalarTower.of_algebraMap_eq fun n => ?_
    show algebraMap ℤ (integralClosure ℤ ℂ) n = χ (algebraMap ℤ (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) n)
    simp only [eq_intCast, map_intCast]
  haveI : Algebra.IsIntegral (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) (integralClosure ℤ ℂ) := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (integralClosure.isIntegral x)
  haveI := h𝔪₁max
  obtain ⟨𝔪', h𝔪'max, h𝔪'comap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := integralClosure ℤ ℂ) 𝔪₁
      (by rw [RingHom.algebraMap_toAlgebra]; exact hkerχ)
  have hmem : ∀ t, t ∈ 𝔪₁ ↔ χ t ∈ 𝔪' := by
    intro t
    rw [← h𝔪'comap, Ideal.mem_comap, RingHom.algebraMap_toAlgebra]
  haveI : 𝔪'.IsMaximal := h𝔪'max
  have hp𝔪' : ((p : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' := by
    have := (hmem _).mp hp𝔪₁
    rwa [map_natCast] at this

  have hχT : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      ((χ (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hℓ hℓN hℓN) : integralClosure ℤ ℂ) : ℂ)
        = ModularFormClass.qCoeff f ℓ := by
    intro ℓ hℓ hℓN
    have hTf : ((CuspForm.heckeAlgebra.T hℓ hℓN hℓN : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = ModularFormClass.qCoeff f ℓ • f := by
      show CuspForm.heckeTLin 2 hℓ hℓN f = ModularFormClass.qCoeff f ℓ • f
      exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ).1 hℓN
    have h2 := hχ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN)
    rw [hTf] at h2
    have hsub : (ModularFormClass.qCoeff f ℓ - (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) : ℂ)) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · exact (sub_eq_zero.mp h0).symm
    · exfalso
      have h1 := hf.qCoeff_one
      rw [h0, CuspForm.coe_zero] at h1
      simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero] at h1

  have hcongr : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ≠ q → W.IsGoodPrimeFor ℓ → ℓ ≠ p →
      χ (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hℓ hℓN hℓN) - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by
    intro ℓ hℓ hℓN hℓq hg hℓp
    have h := (hmem _).mp (hgen𝔪₁ hℓ hℓN hg hℓp hℓq)
    rwa [exitGen, map_sub, map_intCast] at h

  haveI hpF : Fact p.Prime := ⟨hp⟩
  letI kF : Field (integralClosure ℤ ℂ ⧸ 𝔪') := Ideal.Quotient.field 𝔪'
  let φ : integralClosure ℤ ℂ →+* integralClosure ℤ ℂ ⧸ 𝔪' := Ideal.Quotient.mk 𝔪'
  have hφp : ((p : ℕ) : integralClosure ℤ ℂ ⧸ 𝔪') = 0 := by
    rw [← map_natCast φ p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪'
  haveI : CharP (integralClosure ℤ ℂ ⧸ 𝔪') p := by
    have hc := CharP.ringChar_of_prime_eq_zero hp hφp
    exact hc ▸ ringChar.charP (integralClosure ℤ ℂ ⧸ 𝔪')
  letI : Algebra (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪') := ZMod.algebra _ p
  have hℓk : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ≠ p → (ℓ' : integralClosure ℤ ℂ ⧸ 𝔪') ≠ 0 := by
    intro ℓ' hℓ' hℓ'p h0
    rw [CharP.cast_eq_zero_iff (integralClosure ℤ ℂ ⧸ 𝔪') p ℓ'] at h0
    exact hℓ'p ((Nat.prime_dvd_prime_iff_eq hp hℓ').mp h0).symm
  obtain ⟨ρf, hatt, -⟩ := hf.exists_residualGaloisRep_isAttachedTo hp φ
  have htd := (ρf.isAttachedTo_iff_trace_det f φ).mp hatt

  have hΔ : W.Δ ≠ 0 := fun h0 => hqgood (h0.symm ▸ dvd_zero _)
  let E : WeierstrassCurve ℚ := W.map (Int.castRingHom ℚ)
  have hΔE : E.Δ ≠ 0 := by
    show (W.map (Int.castRingHom ℚ)).Δ ≠ 0
    rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero_iff _ (Int.castRingHom ℚ).injective_int).mpr hΔ
  haveI : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔE⟩
  have hWE : W.IsIntegralModelOf E := ⟨1, one_smul _ _⟩
  let ρE := galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p
  have hpK : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfrE : Module.finrank (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = 2 :=
    WeierstrassCurve.finrank_torsionBy_of_isAlgClosed (F := ℚ) E hpK
  obtain ⟨L₁, hL₁, h₁⟩ := ρf.factorsThroughFiniteLevel
  obtain ⟨L₂, hL₂, h₂⟩ := WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel E p
  haveI := hL₁; haveI := hL₂
  obtain ⟨F, iF, iNF, iG, iA, iT, hF⟩ := exists_numberField_ker_restrictNormalHom_le L₂ L₁
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρE.ker ⊓ ρf.ρ.ker := by
    intro τ hτ
    obtain ⟨hx₂, hx₁⟩ := hF τ hτ
    exact Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr (h₂ τ hx₂), MonoidHom.mem_ker.mpr (h₁ τ hx₁)⟩
  have hNqp : N * q * p ≠ 0 := by
    have := NeZero.ne N; have := NeZero.ne q; have := hp.pos; positivity
  set S' : Finset ℕ := (N * q * p).primeFactors ∪ W.Δ.natAbs.primeFactors with hS'
  have hout : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ∉ S' → ¬ ℓ' ∣ N ∧ ℓ' ≠ q ∧ ℓ' ≠ p ∧ W.IsGoodPrimeFor ℓ' := by
    intro ℓ' hℓ' hℓ'S
    have h1 : ℓ' ∉ (N * q * p).primeFactors := fun h => hℓ'S (Finset.mem_union_left _ h)
    have h2 : ℓ' ∉ W.Δ.natAbs.primeFactors := fun h => hℓ'S (Finset.mem_union_right _ h)
    refine ⟨fun hd => h1 (Nat.mem_primeFactors.mpr ⟨hℓ', (hd.mul_right _).mul_right _, hNqp⟩), ?_, ?_, ?_⟩
    · rintro rfl
      exact h1 (Nat.mem_primeFactors.mpr ⟨hℓ', (dvd_mul_left _ _).mul_right _, hNqp⟩)
    · rintro rfl
      exact h1 (Nat.mem_primeFactors.mpr ⟨hℓ', dvd_mul_left _ _, hNqp⟩)
    · intro hd
      exact h2 (Nat.mem_primeFactors.mpr ⟨hℓ', Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr hΔ⟩)
  have htr : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ∉ S' →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ' →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt τ ℓ' →
          algebraMap (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪')
              (LinearMap.trace (ZMod p) _ (ρE τ)) = LinearMap.trace _ ρf.V (ρf.ρ τ) := by
    intro ℓ' hℓ' hℓ'S A' hA' τ hτ
    obtain ⟨hℓ'N, hℓ'q, hℓ'p, hg⟩ := hout ℓ' hℓ' hℓ'S
    obtain ⟨htrE, -⟩ := hWE.galoisTrace_det_frobenius p ℓ' hp hℓ' hℓ'p hg A' hA' τ hτ
    obtain ⟨a, ha, htrg, -⟩ := htd ℓ' hℓ' hℓ'N (hℓk ℓ' hℓ' hℓ'p) A' hA' τ hτ
    have haa : a = χ (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hℓ' hℓ'N hℓ'N) :=
      Subtype.ext (ha.trans (hχT hℓ' hℓ'N).symm)
    rw [galoisTrace_def] at htrE
    have hφ : φ a = φ (((W.apOfModel ℓ' : ℤ) : integralClosure ℤ ℂ)) := by
      rw [haa]; exact (Ideal.Quotient.eq).mpr (hcongr hℓ' hℓ'N hℓ'q hg hℓ'p)
    show algebraMap (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪') (LinearMap.trace (ZMod p) _ (ρE τ)) = _
    rw [htrE, htrg, hφ, map_intCast, map_intCast]
  have hdet : ∀ ℓ' : ℕ, ℓ'.Prime → ℓ' ∉ S' →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ' →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt τ ℓ' →
          algebraMap (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪') (LinearMap.det (ρE τ)) = LinearMap.det (ρf.ρ τ) := by
    intro ℓ' hℓ' hℓ'S A' hA' τ hτ
    obtain ⟨hℓ'N, hℓ'q, hℓ'p, hg⟩ := hout ℓ' hℓ' hℓ'S
    obtain ⟨-, hdetE⟩ := hWE.galoisTrace_det_frobenius p ℓ' hp hℓ' hℓ'p hg A' hA' τ hτ
    obtain ⟨a, -, -, hdetg⟩ := htd ℓ' hℓ' hℓ'N (hℓk ℓ' hℓ' hℓ'p) A' hA' τ hτ
    show algebraMap (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪') (LinearMap.det (ρE τ)) = _
    rw [hdetE, hdetg, map_natCast]

  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat q hq
  have hev := Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
    ρE ρf.ρ hfrE ρf.finrank_eq F hker S' htr hdet σ
  obtain ⟨htrEq, -⟩ := hWE.galoisTrace_det_frobenius p q hp hq hqp hqgood A hA σ hσ
  obtain ⟨a, ha, htrgq, -⟩ := htd q hq hqN (hℓk q hq hqp) A hA σ hσ
  have haq : a = χ (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hq hqN hqN) :=
    Subtype.ext (ha.trans (hχT hq hqN).symm)
  rw [galoisTrace_def] at htrEq
  have hkey : φ (χ (CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hq hqN hqN))
      = φ (((W.apOfModel q : ℤ) : integralClosure ℤ ℂ)) := by
    rw [← haq, ← htrgq, ← hev.1]
    show algebraMap (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪') (LinearMap.trace (ZMod p) _ (ρE σ)) = _
    rw [htrEq, map_intCast, map_intCast]

  refine (hmem _).mpr ?_
  rw [exitGen, map_sub, map_intCast]
  exact (Ideal.Quotient.eq).mp hkey

end
end S_ModularCurve_supportTransfer_jZero
end P2MW
export P2MW.S_ModularCurve_supportTransfer_jZero (solution)
