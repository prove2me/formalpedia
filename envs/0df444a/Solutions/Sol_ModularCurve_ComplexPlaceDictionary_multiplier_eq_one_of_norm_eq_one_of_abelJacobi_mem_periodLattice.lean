-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ec55ab73-68d1-5a69-994b-885d574ecd03

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
import Theorems.Thm_ModularCurve_petersson_mem_periodLattice_iff_re_period_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

open scoped MatrixGroups Real Topology
open UpperHalfPlane Filter

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionary periodAlong period periodLattice exists_eq_const_of_norm_multiplier_eq_one ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice petersson_mem_periodLattice_iff_re_period_int"
namespace UnitaryReciprocity
p2m_open "ModularCurve"

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem tendsto_smul_ofComplex_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) (𝓝[≠] (τ : ℂ))
      (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  have hcont : Tendsto (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) (𝓝 (τ : ℂ))
      (𝓝 ((γ • τ : ℍ) : ℂ)) := by
    have h := (hasDerivAt_smul_ofComplex γ τ).continuousAt.tendsto
    simp only [ofComplex_apply] at h
    exact h
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hcont.mono_left nhdsWithin_le_nhds) ?_
  have hS : {z : ℂ | 0 < z.im} ∈ 𝓝[≠] (τ : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [hS, self_mem_nhdsWithin] with z hz hne
  rw [Set.mem_compl_singleton_iff] at hne ⊢
  intro habs
  apply hne
  have h1 : γ • ofComplex z = γ • τ := UpperHalfPlane.ext habs
  have h2 : ofComplex z = τ := smul_left_cancel γ h1
  rw [← h2, ofComplex_apply_of_im_pos hz, coe_mk]

section Quot

variable {N : ℕ} {F F₀ : ℍ → ℂ} {χ χ₀ : CongruenceSubgroup.Gamma0 N → ℂ} {k : ℍ → ℤ}

structure IsMult (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ) (k : ℍ → ℤ) : Prop where
  mero : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  mult : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ
  unit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1
  cusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)
  ord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = ((k τ : ℤ) : WithTop ℤ)

noncomputable def quot (F F₀ : ℍ → ℂ) : ℂ → ℂ :=
  (fun z : ℂ => F (ofComplex z)) / fun z : ℂ => F₀ (ofComplex z)

noncomputable def U (F F₀ : ℍ → ℂ) : ℂ → ℂ := toMeromorphicNFOn (quot F F₀) {z : ℂ | 0 < z.im}

theorem quot_coe (w : ℍ) : quot F F₀ (w : ℂ) = F w / F₀ w := by
  simp only [quot, Pi.div_apply, ofComplex_apply]

theorem quot_apply (z : ℂ) : quot F F₀ z = F (ofComplex z) / F₀ (ofComplex z) := rfl

theorem quot_meromorphicAt (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    MeromorphicAt (quot F F₀) (τ : ℂ) :=
  (h.mero τ).div (h₀.mero τ)

theorem quot_meromorphicOn (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) :
    MeromorphicOn (quot F F₀) {z : ℂ | 0 < z.im} :=
  fun z hz => quot_meromorphicAt h h₀ ⟨z, hz⟩

theorem quot_order (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    meromorphicOrderAt (quot F F₀) (τ : ℂ) = 0 := by
  have h1 := meromorphicOrderAt_div (h.mero τ) (h₀.mero τ)
  rw [h.ord τ, h₀.ord τ, ← WithTop.LinearOrderedAddCommGroup.coe_sub, sub_self,
    WithTop.coe_zero] at h1
  exact h1

theorem U_nf : MeromorphicNFOn (U F F₀) {z : ℂ | 0 < z.im} :=
  meromorphicNFOn_toMeromorphicNFOn _ _

theorem U_eventuallyEq_quot (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    U F F₀ =ᶠ[𝓝[≠] (τ : ℂ)] quot F F₀ :=
  (quot_meromorphicOn h h₀).toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos

theorem U_order (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    meromorphicOrderAt (U F F₀) (τ : ℂ) = 0 := by
  rw [meromorphicOrderAt_congr (U_eventuallyEq_quot h h₀ τ)]
  exact quot_order h h₀ τ

theorem U_analyticAt (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    AnalyticAt ℂ (U F F₀) (τ : ℂ) :=
  ((U_nf (F := F) (F₀ := F₀)) τ.im_pos).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (U_order h h₀ τ).ge

theorem U_ne_zero (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    U F F₀ (τ : ℂ) ≠ 0 :=
  ((U_nf (F := F) (F₀ := F₀)) τ.im_pos).meromorphicOrderAt_eq_zero_iff.mp (U_order h h₀ τ)

theorem tendsto_quot (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    Tendsto (quot F F₀) (𝓝[≠] (τ : ℂ)) (𝓝 (U F F₀ (τ : ℂ))) :=
  (((U_analyticAt h h₀ τ).continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr'
    (U_eventuallyEq_quot h h₀ τ)

theorem tendsto_quot_smul (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (σ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun z : ℂ => F (σ • ofComplex z) / F₀ (σ • ofComplex z)) (𝓝[≠] (τ : ℂ))
      (𝓝 (U F F₀ ((σ • τ : ℍ) : ℂ))) := by
  have := (tendsto_quot h h₀ (σ • τ)).comp (tendsto_smul_ofComplex_nhdsNE σ τ)
  refine this.congr fun z => ?_
  simp only [Function.comp_apply, quot_coe]

theorem U_smul (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (γ : CongruenceSubgroup.Gamma0 N)
    (τ : ℍ) :
    U F F₀ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = χ γ / χ₀ γ * U F F₀ (τ : ℂ) := by
  have ha := tendsto_quot_smul h h₀ (γ : SL(2, ℤ)) τ
  have hb : Tendsto (fun z : ℂ => χ γ / χ₀ γ * quot F F₀ z) (𝓝[≠] (τ : ℂ))
      (𝓝 (χ γ / χ₀ γ * U F F₀ (τ : ℂ))) :=
    (tendsto_quot h h₀ τ).const_mul _
  have hfun : (fun z : ℂ => F ((γ : SL(2, ℤ)) • ofComplex z) / F₀ ((γ : SL(2, ℤ)) • ofComplex z))
      = fun z : ℂ => χ γ / χ₀ γ * quot F F₀ z := by
    funext z
    rw [h.mult, h₀.mult, quot_apply, mul_div_mul_comm]
  rw [hfun] at ha
  exact tendsto_nhds_unique ha hb

theorem U_tendsto_atImInfty (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (σ : SL(2, ℤ))
    {L L₀ : ℂ} (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hL₀ : Tendsto (fun τ : ℍ => F₀ (σ • τ)) atImInfty (𝓝 L₀)) (hL₀ne : L₀ ≠ 0) :
    Tendsto (fun τ : ℍ => U F F₀ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 (L / L₀)) := by
  have hH : Tendsto (fun τ : ℍ => F (σ • τ) / F₀ (σ • τ)) atImInfty (𝓝 (L / L₀)) :=
    hL.div hL₀ hL₀ne
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ τ : ℍ in atImInfty, dist (F (σ • τ) / F₀ (σ • τ)) (L / L₀) < ε / 2 :=
    Metric.tendsto_nhds.mp hH (ε / 2) (half_pos hε)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  show {τ : ℍ | dist (U F F₀ ((σ • τ : ℍ) : ℂ)) (L / L₀) < ε} ∈ atImInfty
  rw [atImInfty_mem]
  refine ⟨A + 1, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq]

  have hlim := tendsto_quot_smul h h₀ σ τ
  have hS : {z : ℂ | 0 < z.im} ∈ 𝓝[≠] (τ : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have hA' : {z : ℂ | A < z.im} ∈ 𝓝[≠] (τ : ℂ) := by
    apply mem_nhdsWithin_of_mem_nhds
    apply (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    show A < (τ : ℂ).im
    rw [coe_im]
    linarith
  have hin : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ),
      F (σ • ofComplex z) / F₀ (σ • ofComplex z) ∈ Metric.closedBall (L / L₀) (ε / 2) := by
    filter_upwards [hS, hA'] with z hz hzA
    have hmem := hA (ofComplex z) (by
      rw [ofComplex_apply_of_im_pos hz]
      show A ≤ z.im
      exact le_of_lt hzA)
    exact Metric.mem_closedBall.mpr (le_of_lt hmem)
  have hmem : U F F₀ ((σ • τ : ℍ) : ℂ) ∈ Metric.closedBall (L / L₀) (ε / 2) :=
    Metric.isClosed_closedBall.mem_of_tendsto hlim hin
  rw [Metric.mem_closedBall] at hmem
  linarith

theorem multiplier_eq [NeZero N] (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k)
    (γ : CongruenceSubgroup.Gamma0 N) : χ γ = χ₀ γ := by
  have hχ₀ne : ∀ γ : CongruenceSubgroup.Gamma0 N, χ₀ γ ≠ 0 := by
    intro γ h0
    have := h₀.unit γ
    rw [h0, norm_zero] at this
    exact zero_ne_one this

  set Uh : ℍ → ℂ := fun τ => U F F₀ (τ : ℂ) with hUh
  set ψ : CongruenceSubgroup.Gamma0 N → ℂ := fun γ => χ γ / χ₀ γ with hψ
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => Uh (ofComplex z)) {z : ℂ | 0 < z.im} := by
    have hU : DifferentiableOn ℂ (U F F₀) {z : ℂ | 0 < z.im} := fun z hz =>
      (U_analyticAt h h₀ ⟨z, hz⟩).differentiableAt.differentiableWithinAt
    refine hU.congr fun z hz => ?_
    show U F F₀ ((ofComplex z : ℍ) : ℂ) = U F F₀ z
    rw [ofComplex_apply_of_im_pos hz, coe_mk]
  have hmult : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ),
      Uh ((γ : SL(2, ℤ)) • τ) = ψ γ * Uh τ := fun γ τ => U_smul h h₀ γ τ
  have hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖ψ γ‖ = 1 := by
    intro γ
    show ‖χ γ / χ₀ γ‖ = 1
    rw [norm_div, h.unit, h₀.unit, div_one]
  have hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => Uh (σ • τ)) atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hLne, hL⟩ := h.cusp σ
    obtain ⟨L₀, hL₀ne, hL₀⟩ := h₀.cusp σ
    exact ⟨L / L₀, div_ne_zero hLne hL₀ne, U_tendsto_atImInfty h h₀ σ hL hL₀ hL₀ne⟩
  obtain ⟨C, hC⟩ :=
    ModularCurve.exists_eq_const_of_norm_multiplier_eq_one Uh ψ hdiff hmult hunit hcusp
  have hCne : C ≠ 0 := by
    rw [← hC UpperHalfPlane.I]
    exact U_ne_zero h h₀ UpperHalfPlane.I
  have hψ1 : ψ γ = 1 := by
    have hEq : C = ψ γ * C := by
      have h1 := hmult γ UpperHalfPlane.I
      rwa [hC, hC] at h1
    have : (ψ γ - 1) * C = 0 := by rw [sub_mul, one_mul, ← hEq, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hCne
  exact (div_eq_one_iff_eq (hχ₀ne γ)).mp hψ1

end Quot

end ModularCurve.UnitaryReciprocity

open ModularCurve.UnitaryReciprocity in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N)
    (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) : χ γ = 1 := by

  obtain ⟨F₀, χ₀, f, hF₀, hχ₀, hunit₀, hcusp₀, hord₀, hχ₀f, Λ₀, hΛ₀, hrec⟩ :=
    ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
      D c hdeg

  have h : IsMult F χ (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) :=
    ⟨hF, hχ, hunit, hcusp, hord⟩
  have h₀ : IsMult F₀ χ₀ (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) :=
    ⟨hF₀, hχ₀, hunit₀, hcusp₀, hord₀⟩
  rw [multiplier_eq h h₀ γ, hχ₀f γ]

  have hPet : ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g := by
    refine ⟨Λ₀ - c.sum (fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ),
      Submodule.sub_mem _ hΛ₀ hΛ, fun g => ?_⟩
    rw [LinearMap.sub_apply]
    linear_combination hrec g
  obtain ⟨m, hm⟩ := (ModularCurve.petersson_mem_periodLattice_iff_re_period_int f).mp hPet γ
  rw [hm]
  have : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I m

end S_ModularCurve_ComplexPlaceDictionary_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice (solution)
