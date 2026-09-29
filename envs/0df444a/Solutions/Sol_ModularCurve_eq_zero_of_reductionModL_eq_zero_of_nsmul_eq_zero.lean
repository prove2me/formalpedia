-- Prove2me | solution 1 for ModularCurve.eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/71b15ccd-ca6c-518d-9a05-7e29ba249f78

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one"
p2m_attr_erase "simp" "HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsPlaceReductionAlong integralPrincipalDivisors PrincipalGeneratedByIntegral coe_reductionDegZeroAlong IsPlaceReductionModL ReductionInputsModL placeReductionModL isPlaceReductionModL_placeReductionModL reductionModL reductionModL_mk IsPlaceReductionAlong.eq_of_agree modularFunctionFieldBar JZero qExpand qExpand_one_apply algebraMap_apply_eq_single jq dedekindPsi divisorExpansions modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_jqModC jqModC_ne_zero_of_nontrivial divisorExpansionsC modularFunctionFieldFullC jqModC_mem_full jqModC jqModC_rat coeffMap_qExpand coeff_jqModC_neg_one isCurveOver_modularFunctionFieldBar exists_transcendental_finiteDimensional_modularFunctionFieldBar JZero.divisible exists_constantReduction_isGood_isPlaceReductionModL finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi transcendental_jqModC dedekindPsi_pos"
namespace W11TorsionInjectiveRoadC
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve HahnSeries IntermediateField WithZero"

section QAdic

variable (K : Type*) [Field K] (N : ℕ)

def qadicValuation : Valuation (modularFunctionFieldFullC K N) ℤᵐ⁰ :=
  Valued.v.comap (algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K))

theorem qadicValuation_apply (x : modularFunctionFieldFullC K N) :
    qadicValuation K N x = Valued.v (x : LaurentSeries K) := rfl

omit N in
theorem valuation_C_le_one (a : K) : Valued.v (HahnSeries.C a : LaurentSeries K) ≤ 1 := by
  have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0) (f := HahnSeries.C a)).mpr
    (fun n hn => by rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne])
  simpa using h

omit N in
theorem not_valuation_jqModC_le_one : ¬ Valued.v (jqModC K : LaurentSeries K) ≤ 1 := by
  intro h
  have h' : Valued.v (jqModC K : LaurentSeries K) ≤ exp (-(0:ℤ)) := by simpa using h
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero] at h'
  have := h' (-1) (by norm_num)
  rw [coeff_jqModC_neg_one] at this
  exact one_ne_zero this

scoped instance : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (qadicValuation K N))) := by
  have hj : (qadicValuation K N) ⟨jqModC K, jqModC_mem_full K N⟩ ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h => jqModC_ne_zero_of_nontrivial K (congrArg Subtype.val h)
  refine ⟨⟨⟨Units.mk0 _ hj, MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩⟩, 1, ?_⟩⟩
  intro h
  have h2 := congrArg (fun u : (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (qadicValuation K N))) =>
    ((u : (ℤᵐ⁰)ˣ) : ℤᵐ⁰)) h
  simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one] at h2
  exact not_valuation_jqModC_le_one K (le_of_eq h2)

def qadicPlace : Place K (modularFunctionFieldFullC K N) where
  toValuationSubring := (qadicValuation K N).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff, qadicValuation_apply]
    show Valued.v ((algebraMap K (LaurentSeries K)) a) ≤ 1
    rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
    exact valuation_C_le_one K a
  ne_top' h := by
    have : (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∈
        (qadicValuation K N).valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff] at this
    exact not_valuation_jqModC_le_one K this
  isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing _

theorem jqModC_not_mem_qadicPlace :
    (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∉ (qadicPlace K N).toValuationSubring := by
  intro h
  change _ ∈ (qadicValuation K N).valuationSubring at h
  rw [Valuation.mem_valuationSubring_iff] at h
  exact not_valuation_jqModC_le_one K h

theorem ord_ne_zero_of_not_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∉ v.toValuationSubring) : v.ord f ≠ 0 := by
  intro h0
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h0, zpow_zero, mul_one] at hu
  exact hf (hu ▸ (u : v.toValuationSubring).2)

theorem ord_qadicPlace_jqModC_ne_zero :
    (qadicPlace K N).ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ≠ 0 :=
  ord_ne_zero_of_not_mem _ (jqModC_not_mem_qadicPlace K N)

end QAdic

section Generic

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}

theorem degree_eq_zero_of_mem_principal {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this, hdeg]

theorem jqModC_mem_laurentBaseChange [NeZero N] :
    coeffMap A.subtype (jqModC A) ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  rw [coeffMap_jqModC, ← coeffMap_jqModC (algebraMap ℚ L), jqModC_rat]
  have h : jq ∈ modularFunctionFieldFull N := by
    simpa [qExpand_one_apply] using jqd_mem_full (N := N) (one_dvd N)
  exact coeffEmb_mem_laurentBaseChange L h

theorem exists_principal_mapDomain_ne_zero [NeZero N]
    [hPL : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N))]
    {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k (modularFunctionFieldFullC k N)}
    (hr : IsPlaceReductionAlong A π N r) :
    ∃ D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      Finsupp.mapDomain r D ≠ 0 := by
  set xj : laurentBaseChange L (modularFunctionFieldFull N) :=
    ⟨coeffMap A.subtype (jqModC A), jqModC_mem_laurentBaseChange⟩
  have hxj0 : xj ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    rw [show ((0 : laurentBaseChange L (modularFunctionFieldFull N)) : LaurentSeries L) = 0 from rfl] at this
    rw [show (xj : LaurentSeries L) = coeffMap A.subtype (jqModC A) from rfl, coeffMap_jqModC] at this
    exact jqModC_ne_zero_of_nontrivial L this
  obtain ⟨D, hD, -⟩ := hPL.exists_divisor xj hxj0
  refine ⟨D, ⟨xj, hxj0, hD⟩, ?_⟩
  have hyk : coeffMap π (jqModC A) ∈ modularFunctionFieldFullC k N := by
    rw [coeffMap_jqModC]; exact jqModC_mem_full k N
  have hne : coeffMap π (jqModC A) ≠ 0 := by rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial k
  intro h0
  have h1 := congrArg (fun E => E (qadicPlace k N)) h0
  simp only [Finsupp.zero_apply] at h1
  rw [hr.2 (jqModC A) jqModC_mem_laurentBaseChange hyk hne D hD (qadicPlace k N)] at h1
  apply ord_qadicPlace_jqModC_ne_zero k N
  convert h1 using 2
  exact Subtype.ext (coeffMap_jqModC π).symm

theorem mapDomain_eq_of_spec
    {r₁ r₂ : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k (modularFunctionFieldFullC k N)}
    (hr₁ : IsPlaceReductionAlong A π N r₁) (hr₂ : IsPlaceReductionAlong A π N r₂)
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ integralPrincipalDivisors A π N) :
    Finsupp.mapDomain r₁ D = Finsupp.mapDomain r₂ D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  ext Q
  rw [hr₁.2 y hy hyk hne D hDy Q, hr₂.2 y hy hyk hne D hDy Q]

theorem eq_of_spec [NeZero N]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N))]
    {r₁ r₂ : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k (modularFunctionFieldFullC k N)}
    (hr₁ : IsPlaceReductionAlong A π N r₁) (hr₂ : IsPlaceReductionAlong A π N r₂)
    (hgen : PrincipalGeneratedByIntegral A π N)
    (hdeg : ∀ P : Place L (laurentBaseChange L (modularFunctionFieldFull N)), P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)), n • y = x) :
    r₁ = r₂ :=
  IsPlaceReductionAlong.eq_of_agree hgen (fun _ hD => mapDomain_eq_of_spec hr₁ hr₂ hD) hdeg
    (fun _ hD => degree_eq_zero_of_mem_principal hD) hdiv (exists_principal_mapDomain_ne_zero hr₁)

end Generic

section Kummer

open IsLocalRing

theorem natCast_ne_zero_of_dvd {k : Type*} [NonAssocSemiring k] {m q : ℕ}
    (hm : (m : k) ≠ 0) (hq : q ∣ m) : (q : k) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hq
  intro h
  apply hm
  rw [Nat.cast_mul, h, zero_mul]

theorem ne_zero_of_natCast_ne_zero {k : Type*} [NonAssocSemiring k] {m : ℕ}
    (hm : (m : k) ≠ 0) : m ≠ 0 := by
  rintro rfl
  exact hm Nat.cast_zero

theorem eq_zero_of_forall_prime {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ∀ x : G, q • x = 0 → φ x = 0 → x = 0)
    (x : G) (hmx : m • x = 0) (hx : φ x = 0) : x = 0 := by
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using hmx
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m', rfl⟩ := hqm
    have hm' : m' ≠ 0 := by rintro rfl; simp at hm
    have hy : m' • x = 0 := by
      refine h q hq (dvd_mul_right q m') (m' • x) ?_ ?_
      · rw [smul_smul]; exact hmx
      · rw [map_nsmul, hx, nsmul_zero]
    have hlt : m' < q * m' := lt_mul_left (Nat.pos_of_ne_zero hm') hq.one_lt
    exact ih m' hlt hm' (fun q' hq' hq'm => h q' hq' (Dvd.dvd.mul_left hq'm q)) x hy hx

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem nsmul_divisor_apply (m : ℕ) (D : Divisor L F) (P : Place L F) :
    (m • D) P = (m : ℤ) * D P := by
  simp [Finsupp.smul_apply]

theorem smul_const_ne_zero (R : ConstantReduction A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ R.integers) (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mk_eq_zero_of_mem_principal (D : Divisor.degZero (K := L) (F := F))
    (hD : (D : Divisor L F) ∈ Divisor.principal (K := L) (F := F)) : Pic0.mk D = 0 := by
  refine (QuotientAddGroup.eq_zero_iff D).mpr ?_
  rwa [AddSubgroup.mem_addSubgroupOf]

theorem exists_kummerDatum (R : ConstantReduction A F Fbar) (z : Pic0 L F) (m : ℕ)
    (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    ∃ D : Divisor.degZero (K := L) (F := F), Pic0.mk D = z ∧
      ∃ f : R.integers, R.residue f ≠ 0 ∧ (∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (f : F)) ∧
      ∃ g : Fbar, g ≠ 0 ∧ (∀ Q : Place (ResidueField A) Fbar,
        Finsupp.mapDomain R.placeMap (D : Divisor L F) Q = Q.ord g) ∧
      ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hmD : ((m • D : Divisor.degZero (K := L) (F := F)) : Divisor L F) ∈
      Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (m • D) = 0 := by
      change QuotientAddGroup.mk (m • D) = (0 : Pic0 L F)
      rw [QuotientAddGroup.mk_nsmul]
      exact hmz
    have h2 := (QuotientAddGroup.eq_zero_iff (m • D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f₀, hf₀, hDf₀⟩ := hmD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f₀ hf₀
  have hc0 : c ≠ 0 := smul_const_ne_zero R hc hres
  have hdivf : ∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (c • f₀) := fun P => by
    rw [ConstantReduction.ord_smul P hc0, ← hDf₀ P, AddSubgroupClass.coe_nsmul, nsmul_divisor_apply]
  have hrD : (R.degZeroMap D : Divisor (ResidueField A) Fbar) ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) := by
    have h1 : Pic0.mk (R.degZeroMap D) = 0 := by rw [← ConstantReduction.pic0Map_mk]; exact hz
    have h2 := (QuotientAddGroup.eq_zero_iff (R.degZeroMap D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨g, hg, hDg⟩ := hrD
  refine ⟨D, rfl, ⟨c • f₀, hc⟩, hres, hdivf, g, hg, fun Q => by rw [← hDg Q]; rfl, fun Q => ?_⟩
  have key := R.mapDomain_placeMap ⟨c • f₀, hc⟩ hres ((m • D : Divisor.degZero (K := L) (F := F)) :
      Divisor L F) (fun P => by rw [AddSubgroupClass.coe_nsmul, nsmul_divisor_apply, hdivf P]) Q
  rw [← key, AddSubgroupClass.coe_nsmul, Finsupp.mapDomain_smul, nsmul_divisor_apply, ← hDg Q]
  rfl

theorem ord_residue_mul_inv_pow_eq_zero (R : ConstantReduction A F Fbar) {f : R.integers}
    (hf : R.residue f ≠ 0) {g : Fbar} (hg : g ≠ 0) (m : ℕ)
    (h : ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g)
    (Q : Place (ResidueField A) Fbar) : Q.ord (R.residue f * (g ^ m)⁻¹) = 0 := by
  rw [Q.ord_mul hf (inv_ne_zero (pow_ne_zero _ hg)), Q.ord_inv, h Q, ← zpow_natCast,
    Q.ord_zpow]
  ring

theorem mem_principal_of_pow_eq {q : ℕ} (hq : q ≠ 0) {D : Divisor L F} {f h : F} (hf : f ≠ 0)
    (hhf : h ^ q = f) (hD : ∀ P, (q : ℤ) * D P = P.ord f) :
    D ∈ Divisor.principal (K := L) (F := F) := by
  have hh : h ≠ 0 := by
    rintro rfl
    rw [zero_pow hq] at hhf
    exact hf hhf.symm
  refine ⟨h, hh, fun P => ?_⟩
  have h1 : (q : ℤ) * D P = (q : ℤ) * P.ord h := by
    rw [hD P, ← hhf, ← zpow_natCast, P.ord_zpow]
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hq) h1

theorem prime_case [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (q : ℕ) [hqp : Fact q.Prime] (hqk : (q : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hqz : q • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  classical
  have hq0 : q ≠ 0 := hqp.out.ne_zero
  have hqpos : 0 < q := hqp.out.pos

  obtain ⟨D, hDz, f, hfres, hdivf, g, hg0, -, hordfg⟩ := exists_kummerDatum R z q hqz hz
  subst hDz
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hfres
    rw [show f = 0 from Subtype.ext h, map_zero]

  obtain ⟨xO, hxt, hxpos, hxeq⟩ := hreg
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue xO} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hxpos
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set u : Fbar := R.residue f * (g ^ q)⁻¹ with hu
  have hu_ord : ∀ Q' : Place (ResidueField A) Fbar, Q'.ord u = 0 :=
    ord_residue_mul_inv_pow_eq_zero R hfres hg0 q hordfg
  obtain ⟨cbar, hcbar⟩ :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (R.residue xO) hxt hu_ord
  obtain ⟨ebar, hebar⟩ := IsAlgClosed.exists_pow_nat_eq cbar hqpos
  set w : Fbar := algebraMap (ResidueField A) Fbar ebar * g with hw
  have hwq : w ^ q = R.residue f := by
    rw [hw, mul_pow, ← map_pow, hebar, hcbar, hu, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hg0), mul_one]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hfres
    rw [← hwq, h0, zero_pow hq0]

  have hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F) := fun P => ⟨_, (hdivf P).symm⟩
  have hgood : genusFF (ResidueField A) Fbar = genusFF L F := (R.isGood_iff).mp hR
  obtain ⟨h, hh⟩ := RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    A hF R.toRegularProlongation hgood ⟨xO, hxt, hxpos, hxeq⟩ hqk f hdvd w hw0 hwq
  exact mk_eq_zero_of_mem_principal D (mem_principal_of_pow_eq hq0 hf0 hh hdivf)

theorem of_finrank_eq [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (m : ℕ) (hm : (m : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  refine eq_zero_of_forall_prime R.pic0Map m (ne_zero_of_natCast_ne_zero hm)
    (fun q hq hqm z' hqz hz' => ?_) z hmz hz
  haveI : Fact q.Prime := ⟨hq⟩
  exact prime_case A F hF Fbar R hR hreg q (natCast_ne_zero_of_dvd hm hqm) z' hqz hz'

end Kummer

section Generators

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

def gens : Set (LaurentSeries L) := ⇑(coeffEmb L) '' divisorExpansions N

theorem adjoin_gens_le : adjoin L (gens L N) ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  change adjoin L (gens L N) ≤ adjoin L _
  refine adjoin.mono L _ _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, IntermediateField.subset_adjoin ℚ _ hx, rfl⟩

theorem laurentBaseChange_le_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) ≤ adjoin L (gens L N) := by
  change adjoin L _ ≤ adjoin L (gens L N)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gens L N)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gens L N)).algebraMap_mem _
  · exact IntermediateField.subset_adjoin L _ ⟨z, hz, rfl⟩

theorem laurentBaseChange_eq_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) = adjoin L (gens L N) :=
  le_antisymm (laurentBaseChange_le_adjoin_gens L N) (adjoin_gens_le L N)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

theorem gens_eq_divisorExpansionsC : gens L N = divisorExpansionsC L N := by
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, coeffEmb_qExpand_jq L d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨_, ⟨d, hd, hdN, rfl⟩, coeffEmb_qExpand_jq L d⟩

theorem laurentBaseChange_eq_fullC :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  rw [laurentBaseChange_eq_adjoin_gens, gens_eq_divisorExpansionsC]; rfl

theorem finrank_adjoin_transport {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem finrank_adjoin_j_laurentBaseChange (hN : (N : L) ≠ 0)
    (hj : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N)) :
    Module.finrank (IntermediateField.adjoin L
        ({(⟨jqModC L, hj⟩ : laurentBaseChange L (modularFunctionFieldFull N))} :
          Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (laurentBaseChange L (modularFunctionFieldFull N)) = dedekindPsi N := by
  rw [finrank_adjoin_transport L (laurentBaseChange_eq_fullC L N) hj (jqModC_mem_full L N)]
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi L N hN

end Generators

theorem finrank_congr_of_eq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {M M' : IntermediateField K E} (h : M = M') : Module.finrank M E = Module.finrank M' E := by
  subst h; rfl

theorem adjoin_smul_eq {K E : Type*} [Field K] [Field E] [Algebra K E] {a : K} (ha : a ≠ 0) (y : E) :
    IntermediateField.adjoin K ({a • y} : Set E) = IntermediateField.adjoin K ({y} : Set E) := by
  refine le_antisymm (adjoin_simple_le_iff.mpr ?_) (adjoin_simple_le_iff.mpr ?_)
  · rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) (mem_adjoin_simple_self K y)
  · have h := mul_mem (inv_mem (IntermediateField.algebraMap_mem
      (IntermediateField.adjoin K ({a • y} : Set E)) a)) (mem_adjoin_simple_self K (a • y))
    have hy : (algebraMap K E a)⁻¹ * (a • y) = y := by
      rw [Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr ha), one_mul]
    rwa [hy] at h

theorem transcendental_smul {K E : Type*} [Field K] [Field E] [Algebra K E] {a : K} (ha : a ≠ 0)
    {y : E} (hy : Transcendental K y) : Transcendental K (a • y) := by
  intro halg
  apply hy
  have h1 : IsAlgebraic K ((algebraMap K E a)⁻¹ * (a • y)) :=
    (isAlgebraic_algebraMap a).inv.mul halg
  rwa [Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr ha), one_mul] at h1

section Modular

theorem natCast_residueField_ne_zero {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) {m : ℕ} (hm : ¬ ℓ ∣ m) : (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (ℓ : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

theorem transcendental_jbar (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Transcendental K (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) :=
  fun h => transcendental_jqModC K
    ((isAlgebraic_algHom_iff (modularFunctionFieldFullC K N).val Subtype.val_injective).mpr h)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_residue_smul_j_eq (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : IsPlaceReductionModL A N R.placeMap)
    (hjmem : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N) :
    ∃ (c : AlgebraicClosure ℚ) (hc : c • (⟨coeffMap A.subtype (jqModC A), hjmem⟩ :
        modularFunctionFieldBar N) ∈ R.integers) (a : IsLocalRing.ResidueField A),
      c ≠ 0 ∧ a ≠ 0 ∧ R.residue ⟨_, hc⟩ =
        a • (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
          modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hPL : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  have hxjL : jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := by
    have := hjmem; rwa [coeffMap_jqModC] at this
  have hxj_eq : (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N) =
      ⟨jqModC (AlgebraicClosure ℚ), hxjL⟩ := Subtype.ext (coeffMap_jqModC A.subtype)
  have hxj0 : (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N) ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    rw [hxj_eq] at this
    exact jqModC_ne_zero_of_nontrivial (AlgebraicClosure ℚ) this
  have hjb0 : (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ≠ 0 :=
    fun h => jqModC_ne_zero_of_nontrivial _ (congrArg Subtype.val h)
  have hjbtr := transcendental_jbar (IsLocalRing.ResidueField A) N
  have hNk : (N : IsLocalRing.ResidueField A) ≠ 0 := natCast_residueField_ne_zero A hA hℓN
  have hfin_k := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
    (IsLocalRing.ResidueField A) N hNk
  haveI : FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)} : Set _))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
    Module.finite_of_finrank_pos (by rw [hfin_k]; exact dedekindPsi_pos N (NeZero.ne N))

  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem _ hxj0
  have hc0 : c ≠ 0 := smul_const_ne_zero R hc hres

  obtain ⟨D, hD, -⟩ := hPL.exists_divisor _ hxj0
  have hDx : ∀ P, D P = P.ord ((⟨_, hc⟩ : R.integers) : modularFunctionFieldBar N) := fun P => by
    rw [hD P]; exact (ConstantReduction.ord_smul P hc0 _).symm
  have h1 : ∀ Q, Finsupp.mapDomain R.placeMap D Q = Q.ord (R.residue ⟨_, hc⟩) :=
    R.mapDomain_placeMap ⟨_, hc⟩ hres D hDx
  have hyk : coeffMap (IsLocalRing.residue A) (jqModC A) ∈
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N := by
    rw [coeffMap_jqModC]; exact jqModC_mem_full _ N
  have hne : coeffMap (IsLocalRing.residue A) (jqModC A) ≠ 0 := by
    rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial _
  have h2 : ∀ Q, Finsupp.mapDomain R.placeMap D Q =
      Q.ord (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := fun Q => by
    rw [hR.2 (jqModC A) hjmem hyk hne D hD Q]
    congr 1
    exact Subtype.ext (coeffMap_jqModC _)

  have hw0 : R.residue ⟨_, hc⟩ ≠ 0 := hres
  have hord : ∀ Q : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      Q.ord (R.residue ⟨_, hc⟩ * (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)⁻¹) = 0 := fun Q => by
    rw [Q.ord_mul hw0 (inv_ne_zero hjb0), Q.ord_inv, ← h1 Q, h2 Q]; ring
  obtain ⟨a, ha⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed _ hjbtr hord
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hw0 (inv_ne_zero hjb0) ha.symm
  refine ⟨c, hc, a, hc0, ha0, ?_⟩
  rw [Algebra.smul_def a, ha, mul_assoc, inv_mul_cancel₀ hjb0, mul_one]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem defectless_of_residue_eq_smul (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hjmem : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N)
    {c : AlgebraicClosure ℚ} (hc : c • (⟨coeffMap A.subtype (jqModC A), hjmem⟩ :
        modularFunctionFieldBar N) ∈ R.integers) {a : IsLocalRing.ResidueField A}
    (hc0 : c ≠ 0) (ha0 : a ≠ 0) (hwa : R.residue ⟨_, hc⟩ =
        a • (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
          modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
    Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨_, hc⟩) ∧
      0 < Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue ⟨_, hc⟩} : Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
          (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ∧
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(((⟨_, hc⟩ : R.integers) : modularFunctionFieldBar N))} : Set (modularFunctionFieldBar N)))
            (modularFunctionFieldBar N) =
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({R.residue ⟨_, hc⟩} : Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
            (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by
  have hxjL : jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := by
    have := hjmem; rwa [coeffMap_jqModC] at this
  have hxj_eq : (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N) =
      ⟨jqModC (AlgebraicClosure ℚ), hxjL⟩ := Subtype.ext (coeffMap_jqModC A.subtype)
  have hjbtr := transcendental_jbar (IsLocalRing.ResidueField A) N
  have hNk : (N : IsLocalRing.ResidueField A) ≠ 0 := natCast_residueField_ne_zero A hA hℓN
  have hfin_k := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
    (IsLocalRing.ResidueField A) N hNk
  have hfin_L : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N)} :
        Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) = dedekindPsi N := by
    rw [hxj_eq]
    exact finrank_adjoin_j_laurentBaseChange (AlgebraicClosure ℚ) N
      (Nat.cast_ne_zero.mpr (NeZero.ne N)) hxjL
  rw [show (((⟨_, hc⟩ : R.integers) : modularFunctionFieldBar N)) =
      c • (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N) from rfl,
    finrank_congr_of_eq (adjoin_smul_eq hc0
      (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N)), hfin_L, hwa,
    finrank_congr_of_eq (adjoin_smul_eq ha0
      (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full _ N⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)), hfin_k]
  exact ⟨transcendental_smul ha0 hjbtr, dedekindPsi_pos N (NeZero.ne N), rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_defectless_witness (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : IsPlaceReductionModL A N R.placeMap) :
    ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue x} : Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
          (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ∧
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(x : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) =
        Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({R.residue x} : Set (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
            (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by
  obtain ⟨c, hc, a, hc0, ha0, hwa⟩ :=
    exists_residue_smul_j_eq N hℓN A hA R hR jqModC_mem_laurentBaseChange
  exact ⟨⟨_, hc⟩, defectless_of_residue_eq_smul N hℓN A hA R jqModC_mem_laurentBaseChange hc hc0 ha0 hwa⟩

set_option synthInstance.maxHeartbeats 1600000 in
theorem main (N : ℕ) [NeZero N] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsModL A N) (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JZero N)
    (hmz : m • z = 0) (hz : ModularCurve.reductionModL A N z = 0) :
    z = 0 := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Ring.KrullDimLE 1 A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A

  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
  have hdeg : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hF := exists_transcendental_finiteDimensional_modularFunctionFieldBar N
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N), n • y = x :=
    fun n hn x => ModularCurve.JZero.divisible N n hn x

  obtain ⟨R, hRgood, hR⟩ := exists_constantReduction_isGood_isPlaceReductionModL N hℓN A hA

  have hr₀ : IsPlaceReductionModL A N (placeReductionModL h) := isPlaceReductionModL_placeReductionModL h
  have hgen : PrincipalGeneratedByIntegral A (IsLocalRing.residue A) N := h.choose_spec.2

  have key : placeReductionModL h = R.placeMap := eq_of_spec hr₀ hR hgen hdeg hdiv

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hRz : R.pic0Map (Pic0.mk D) = 0 := by
    rw [reductionModL_mk h] at hz
    rw [ConstantReduction.pic0Map_mk, ← hz]
    congr 1
    apply Subtype.ext
    rw [ConstantReduction.coe_degZeroMap, coe_reductionDegZeroAlong, key]

  have hreg := exists_defectless_witness N hℓN A hA R hR
  exact of_finrank_eq A (modularFunctionFieldBar N) hF
    (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) R hRgood hreg m
    (natCast_residueField_ne_zero A hA hm) (Pic0.mk D) hmz hRz

end Modular

end ModularCurve.W11TorsionInjectiveRoadC
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve.W11TorsionInjectiveRoadC"
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve"

theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsModL A N) (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JZero N)
    (hmz : m • z = 0) (hz : ModularCurve.reductionModL A N z = 0) :
    z = 0 :=
  ModularCurve.W11TorsionInjectiveRoadC.main N hℓN A hA h m hm z hmz hz

end
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.ModularCurve.W11TorsionInjectiveRoadC"

end S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero (solution)
