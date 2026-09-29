-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f39b1554-1664-5bad-873d-bd0ff405f8d1

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_period
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_period_eq_zero
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero
import Theorems.Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
import Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

open scoped MatrixGroups
open UpperHalfPlane Filter Topology MeasureTheory

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionary periodAlong period periodLattice exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive exists_isParabolicHom_apply_eq_period eq_zero_of_forall_re_period_eq_zero finrank_parabolicHoms_le_two_mul_finrank_cuspForm ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero exists_meromorphic_smul_eq_mul_of_slashInvariant_residue exists_cuspForm_petersson_eq ComplexPlaceDictionary.multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero"
namespace AbelReciprocityThirdKind
p2m_open "ModularCurve"

open ModularCurve.Period

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

theorem exists_col_eq {p r : ℤ} (h : IsCoprime p r) :
    ∃ δ : SL(2, ℤ), δ 0 0 = p ∧ δ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

theorem eq_T_zpow_of_col {M : SL(2, ℤ)} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) :
    M = ModularGroup.T ^ (M 0 1) := by
  have hdet := det_entries M
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_T_zpow]

theorem exists_isCoprime_fixed {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hc : γ 1 0 ≠ 0) :
    ∃ p r : ℤ, IsCoprime p r ∧
      γ 0 0 * p + γ 0 1 * r = p ∧ γ 1 0 * p + γ 1 1 * r = r := by
  rw [Matrix.trace_fin_two] at htr
  have hdet := det_entries γ
  have hgcd_pos : 0 < Int.gcd (γ 0 0 - 1) (γ 1 0) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (γ 0 0 - 1) (γ 1 0)) with h | h
    · exact absurd (Int.gcd_eq_zero_iff.mp h).2 hc
    · exact h
  obtain ⟨p, r, hpr, hp, hr⟩ := Int.exists_gcd_one hgcd_pos
  set g : ℤ := (Int.gcd (γ 0 0 - 1) (γ 1 0) : ℤ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact_mod_cast hgcd_pos.ne'
  refine ⟨p, r, Int.isCoprime_iff_gcd_eq_one.mpr hpr, ?_, ?_⟩
  · have key : g * (γ 0 0 * p + γ 0 1 * r - p) = 0 := by
      linear_combination (-(γ 0 0 - 1)) * hp - γ 0 1 * hr + γ 0 0 * htr - hdet
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith
  · have key : g * (γ 1 0 * p + γ 1 1 * r - r) = 0 := by
      linear_combination (-(γ 1 0)) * hp - (γ 1 1 - 1) * hr + γ 1 0 * htr
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

theorem exists_conj_T_zpow_of_trace_eq_two {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * ModularGroup.T ^ n * δ⁻¹ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at htr
    have hsq : (γ 0 0 - 1) ^ 2 = 0 := by
      linear_combination γ 0 0 * htr - hdet
    have ha : γ 0 0 = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨1, γ 0 1, ?_⟩
    rw [inv_one, mul_one, one_mul]
    exact eq_T_zpow_of_col ha hc
  · obtain ⟨p, r, hpr, hfix1, hfix2⟩ := exists_isCoprime_fixed htr hc
    obtain ⟨δ, hδ00, hδ10⟩ := exists_col_eq hpr
    obtain ⟨hi00, hi01, hi10, hi11⟩ := inv_entries δ
    have hδdet := det_entries δ
    rw [hδ00, hδ10] at hδdet
    have hγδ0 : (γ * δ) 0 0 = δ 0 0 := by
      rw [mul_entry γ δ 0 0, hδ00, hδ10]; exact hfix1
    have hγδ1 : (γ * δ) 1 0 = δ 1 0 := by
      rw [mul_entry γ δ 1 0, hδ00, hδ10]; exact hfix2
    have hM00 : (δ⁻¹ * (γ * δ)) 0 0 = 1 := by
      rw [mul_entry δ⁻¹ (γ * δ) 0 0, hγδ0, hγδ1, hi00, hi01, hδ00, hδ10]
      linear_combination hδdet
    have hM10 : (δ⁻¹ * (γ * δ)) 1 0 = 0 := by
      rw [mul_entry δ⁻¹ (γ * δ) 1 0, hγδ0, hγδ1, hi10, hi11, hδ00, hδ10]
      ring
    refine ⟨δ, (δ⁻¹ * (γ * δ)) 0 1, ?_⟩
    rw [← eq_T_zpow_of_col hM00 hM10]
    group

theorem parabolic_classification (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (n : ℤ), (ε = 1 ∨ ε = -1) ∧
      γ = ε * (δ * ModularGroup.T ^ n * δ⁻¹) := by
  have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsplit with h | h
  · obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two (γ := γ) (by linarith)
    exact ⟨1, δ, n, Or.inl rfl, by rw [one_mul]; exact hδ⟩
  · have htrneg : ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
      linarith
    obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two htrneg
    refine ⟨-1, δ, n, Or.inr rfl, ?_⟩
    rw [neg_one_mul, ← hδ, neg_neg]

theorem conj_T_zpow_smul (δ ε : SL(2, ℤ)) (n : ℤ) (hε : ε = 1 ∨ ε = -1) (w : ℍ) :
    (ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)
      = δ • (((n : ℤ) : ℝ) +ᵥ w) := by
  have hcentral : (ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)
      = (δ * ModularGroup.T ^ n * δ⁻¹) • ((δ : SL(2, ℤ)) • w) := by
    rcases hε with hε | hε
    · rw [hε, one_mul]
    · rw [hε, neg_one_mul]
      exact ModularGroup.SL_neg_smul _ _
  rw [hcentral, ← mul_smul, ← UpperHalfPlane.modular_T_zpow_smul, ← mul_smul]
  congr 1
  group

section FG

variable (N : ℕ)

local notation "Γ" => CongruenceSubgroup.Gamma0 N

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem fg_Gamma0 [NeZero N] : Group.FG Γ := by
  haveI := fg_SL2Z
  infer_instance

theorem addMonoidHom_eq_of_eqOn_gen {A : Type*} [AddCommGroup A] {S : Set Γ}
    (hS : Subgroup.closure S = ⊤) (φ ψ : Additive Γ →+ A)
    (h : ∀ s ∈ S, φ (Additive.ofMul s) = ψ (Additive.ofMul s)) : φ = ψ := by
  suffices H : ∀ γ ∈ Subgroup.closure S, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) by
    ext x
    exact H (Additive.toMul x) (by rw [hS]; exact Subgroup.mem_top _)
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => change φ 0 = ψ 0; rw [map_zero, map_zero]
  | mul y z _ _ hy hz =>
    have : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
    change φ (Additive.ofMul (y * z)) = ψ (Additive.ofMul (y * z))
    rw [this, map_add, map_add]
    exact congrArg₂ (· + ·) hy hz
  | inv y _ hy =>
    have : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
    change φ (Additive.ofMul y⁻¹) = ψ (Additive.ofMul y⁻¹)
    rw [this, map_neg, map_neg]
    exact congrArg Neg.neg hy

theorem finite_addMonoidHom_real [NeZero N] : Module.Finite ℝ (Additive Γ →+ ℝ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma0 N)
  haveI : Fintype S := hSfin.fintype
  let res : (Additive Γ →+ ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun φ s => φ (Additive.ofMul (s : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective res ?_
  intro φ ψ hφψ
  refine addMonoidHom_eq_of_eqOn_gen N hS φ ψ fun s hs => ?_
  exact congrFun hφψ ⟨s, hs⟩

end FG

section RealES

variable (N : ℕ) [NeZero N]

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "V" => CuspForm (CongruenceSubgroup.Gamma0 N) 2

theorem exists_cuspForm_re_period_eq (φ : Additive Γ →+ ℝ) (hφ : IsParabolicHom Γ φ) :
    ∃ f : V, ∀ γ : Γ, (ModularCurve.period N γ f).re = φ (Additive.ofMul γ) := by
  classical
  haveI : FiniteDimensional ℂ V := CuspForm.finiteDimensional_Gamma0 N 2
  haveI : Module.Finite ℝ (Additive Γ →+ ℝ) := finite_addMonoidHom_real N
  obtain ⟨Φ, hΦpar, hΦ⟩ := ModularCurve.exists_isParabolicHom_apply_eq_period N

  let reΦ : V → (Additive Γ →+ ℝ) := fun f =>
    { toFun := fun x => (Φ x f).re
      map_zero' := by simp only [map_zero, LinearMap.zero_apply, Complex.zero_re]
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply, Complex.add_re] }
  have hreΦ : ∀ f x, reΦ f x = (Φ x f).re := fun f x => rfl
  have hreΦpar : ∀ f, IsParabolicHom Γ (reΦ f) := by
    intro f γ hγ
    rw [hreΦ, hΦpar γ hγ, LinearMap.zero_apply, Complex.zero_re]

  let Ψ : V →ₗ[ℝ] parabolicHoms ℝ Γ ℝ :=
    { toFun := fun f => ⟨reΦ f, hreΦpar f⟩
      map_add' := fun f g => by
        refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, hreΦ, map_add, Complex.add_re]
      map_smul' := fun r f => by
        refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
        simp only [Submodule.coe_smul, AddMonoidHom.smul_apply, RingHom.id_apply, hreΦ,
          smul_eq_mul]
        rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul] }
  have hΨ : ∀ (f : V) (γ : Γ),
      ((Ψ f : parabolicHoms ℝ Γ ℝ) : Additive Γ →+ ℝ) (Additive.ofMul γ) =
        (ModularCurve.period N γ f).re := by
    intro f γ
    change reΦ f (Additive.ofMul γ) = _
    rw [hreΦ, hΦ]

  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine ModularCurve.eq_zero_of_forall_re_period_eq_zero N f fun γ => ?_
    rw [← hΨ, hf]
    rfl

  have hrange : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [LinearMap.finrank_range_of_inj hinj, finrank_real_of_complex]
    exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm N
  have hmem : (⟨φ, hφ⟩ : parabolicHoms ℝ Γ ℝ) ∈ LinearMap.range Ψ := by
    rw [hrange]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := hmem
  refine ⟨f, fun γ => ?_⟩
  rw [← hΨ, hf]

end RealES

section Multiplier

variable {N : ℕ} {F : ℍ → ℂ} {χ : CongruenceSubgroup.Gamma0 N → ℂ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N

theorem exists_apply_ne_zero
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ τ : ℍ, F τ ≠ 0 := by
  obtain ⟨L, hL, hlim⟩ := hcusp 1
  obtain ⟨τ, hτ⟩ := (hlim.eventually_ne hL).exists
  exact ⟨τ, by simpa only [one_smul] using hτ⟩

theorem multiplier_one
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    {τ₀ : ℍ} (h0 : F τ₀ ≠ 0) : χ 1 = 1 := by
  have h := hχ 1 τ₀
  rw [OneMemClass.coe_one, one_smul] at h
  exact (mul_right_cancel₀ h0 ((one_mul _).trans h)).symm

theorem multiplier_mul
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    {τ₀ : ℍ} (h0 : F τ₀ ≠ 0) (γ δ : Γ) : χ (γ * δ) = χ γ * χ δ := by
  have h1 := hχ (γ * δ) τ₀
  have h2 : F (((γ * δ : Γ) : SL(2, ℤ)) • τ₀) = χ γ * (χ δ * F τ₀) := by
    rw [show ((γ * δ : Γ) : SL(2, ℤ)) • τ₀ = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • τ₀) by
      rw [← mul_smul]; rfl, hχ, hχ]
  exact mul_right_cancel₀ h0 ((h1.symm.trans h2).trans (mul_assoc _ _ _).symm)

theorem multiplier_ne_zero
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    {τ₀ : ℍ} (h0 : F τ₀ ≠ 0) (γ : Γ) : χ γ ≠ 0 := by
  have h : χ γ * χ γ⁻¹ = 1 := by
    rw [← multiplier_mul hχ h0, mul_inv_cancel, multiplier_one hχ h0]
  exact left_ne_zero_of_mul_eq_one h

theorem multiplier_eq_one_of_trace_sq
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (γ : Γ) (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : χ γ = 1 := by
  obtain ⟨ε, δ, n, hε, hγeq⟩ := parabolic_classification (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL0, hlim⟩ := hcusp δ
  have hlim1 : Tendsto (fun w : ℍ => F ((γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)))
      atImInfty (𝓝 L) := by
    have hfun : (fun w : ℍ => F ((γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)))
        = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
      funext w
      rw [Function.comp_apply, hγeq, conj_T_zpow_smul δ ε n hε w]
    rw [hfun]
    exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))
  have hlim2 : Tendsto (fun w : ℍ => F ((γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)))
      atImInfty (𝓝 (χ γ * L)) := by
    have hfun : (fun w : ℍ => F ((γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)))
        = fun w : ℍ => χ γ * F (δ • w) := funext fun w => hχ γ _
    rw [hfun]
    exact hlim.const_mul _
  have h : χ γ * L = L := tendsto_nhds_unique hlim2 hlim1
  have h' : (χ γ - 1) * L = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hL0

end Multiplier

section Main

variable {N : ℕ} [NeZero N]

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "V" => CuspForm (CongruenceSubgroup.Gamma0 N) 2

theorem exists_unitary (m : ℍ → ℤ) (F : ℍ → ℂ) (χ : Γ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (m τ : WithTop ℤ)) :
    ∃ (F₁ : ℍ → ℂ) (χ₁ : Γ → ℂ),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F₁ (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F₁ ((γ : SL(2, ℤ)) • τ) = χ₁ γ * F₁ τ) ∧
      (∀ γ : Γ, ‖χ₁ γ‖ = 1) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F₁ (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F₁ (ofComplex z)) (τ : ℂ) =
        (m τ : WithTop ℤ)) := by
  classical

  obtain ⟨τ₀, hτ₀⟩ := exists_apply_ne_zero hcusp
  have hone : χ 1 = 1 := multiplier_one hχ hτ₀
  have hmul : ∀ γ δ : Γ, χ (γ * δ) = χ γ * χ δ := multiplier_mul hχ hτ₀
  have hne : ∀ γ : Γ, χ γ ≠ 0 := multiplier_ne_zero hχ hτ₀
  have hpar : ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → χ γ = 1 :=
    multiplier_eq_one_of_trace_sq hχ hcusp

  let φ : Additive Γ →+ ℝ :=
    { toFun := fun x => Real.log ‖χ (Additive.toMul x)‖
      map_zero' := by
        change Real.log ‖χ 1‖ = 0
        rw [hone, norm_one, Real.log_one]
      map_add' := fun x y => by
        change Real.log ‖χ (Additive.toMul x * Additive.toMul y)‖ = _
        rw [hmul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne _))
          (norm_ne_zero_iff.mpr (hne _))] }
  have hφ : ∀ γ : Γ, φ (Additive.ofMul γ) = Real.log ‖χ γ‖ := fun γ => rfl
  have hφpar : IsParabolicHom Γ φ := fun γ hγ => by
    rw [hφ, hpar γ hγ, norm_one, Real.log_one]

  obtain ⟨f₁, hf₁⟩ := exists_cuspForm_re_period_eq N φ hφpar

  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_hasEquivariantPrimitive N f₁
  have hΦper : ∀ (γ : Γ) (τ : ℍ),
      Φ ((γ : SL(2, ℤ)) • τ) = Φ τ + ModularCurve.period N γ f₁ := by
    intro γ τ
    rw [ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N f₁ hΦ γ]
    have h := hΦ.2.2.1.sub_eq_period γ τ
    have h' : hΦ.2.2.1.period γ = Φ ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - Φ UpperHalfPlane.I :=
      rfl
    rw [h'] at h
    linear_combination h

  have hG : ∀ τ : ℍ, AnalyticAt ℂ (fun z : ℂ => Complex.exp (-Φ (ofComplex z))) (τ : ℂ) := by
    intro τ
    have hdiff : DifferentiableOn ℂ (Φ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
      intro z hz
      exact (hΦ.1 ⟨z, hz⟩).differentiableAt.differentiableWithinAt
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have han : AnalyticAt ℂ (Φ ∘ ofComplex) (τ : ℂ) :=
      hdiff.analyticAt (hopen.mem_nhds τ.im_pos)
    exact han.neg.cexp'

  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : ℍ → ℂ, F₁ = fun τ => F τ * Complex.exp (-Φ τ) := ⟨_, rfl⟩
  obtain ⟨χ₁, hχ₁def⟩ :
      ∃ χ₁ : Γ → ℂ, χ₁ = fun γ => χ γ * Complex.exp (-ModularCurve.period N γ f₁) := ⟨_, rfl⟩
  have hprod : (fun z : ℂ => F₁ (ofComplex z)) =
      (fun z : ℂ => F (ofComplex z)) * fun z : ℂ => Complex.exp (-Φ (ofComplex z)) := by
    rw [hF₁def]; rfl
  have hF₁ : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F₁ (ofComplex z)) (τ : ℂ) := fun τ => by
    rw [hprod]
    exact (hF τ).mul (hG τ).meromorphicAt
  have hord₁ : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F₁ (ofComplex z)) (τ : ℂ) =
      (m τ : WithTop ℤ) := by
    intro τ
    have h0 : analyticOrderAt (fun z : ℂ => Complex.exp (-Φ (ofComplex z))) (τ : ℂ) = 0 :=
      (hG τ).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
    rw [hprod, meromorphicOrderAt_mul (hF τ) (hG τ).meromorphicAt, hord τ,
      (hG τ).meromorphicOrderAt_eq, h0, ENat.map_zero, Nat.cast_zero, WithTop.coe_zero,
      add_zero]
  have hχ₁ : ∀ (γ : Γ) (τ : ℍ), F₁ ((γ : SL(2, ℤ)) • τ) = χ₁ γ * F₁ τ := by
    intro γ τ
    rw [hF₁def, hχ₁def]
    dsimp only
    rw [hχ γ τ, hΦper γ τ, neg_add, Complex.exp_add]
    ring
  have hunit₁ : ∀ γ : Γ, ‖χ₁ γ‖ = 1 := by
    intro γ
    rw [hχ₁def]
    dsimp only
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hf₁ γ, hφ, Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr (hne γ)), mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne γ))]
  have hcusp₁ : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F₁ (σ • τ)) atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hL0, hL⟩ := hcusp σ
    obtain ⟨L', hL'⟩ := hΦ.2.2.2 σ
    refine ⟨L * Complex.exp (-L'), mul_ne_zero hL0 (Complex.exp_ne_zero _), ?_⟩
    rw [hF₁def]
    exact hL.mul hL'.neg.cexp
  exact ⟨F₁, χ₁, hF₁, hχ₁, hunit₁, hcusp₁, hord₁⟩

theorem main (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ)) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N,
        χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ f).re : ℂ))) ∧
      ∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g := by
  classical

  obtain ⟨ω, hωΓ, hωcusp, hωres⟩ :=
    ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero D c hdeg

  obtain ⟨F₀, χ₀, hF₀, hχ₀, hcusp₀, hord₀⟩ :=
    ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
      (CongruenceSubgroup.Gamma0 N)
      (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) ω hωΓ hωcusp hωres

  obtain ⟨F, χ, hF, hχ, hunit, hcusp, hord⟩ := exists_unitary _ F₀ χ₀ hF₀ hχ₀ hcusp₀ hord₀

  obtain ⟨f, hf⟩ := ModularCurve.exists_cuspForm_petersson_eq
    (-(c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ))
  have hf0 : ∀ g : V,
      (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = 0 := by
    intro g
    rw [hf g, LinearMap.neg_apply, add_neg_cancel]

  have hrec :=
    ModularCurve.ComplexPlaceDictionary.multiplier_eq_exp_of_abelJacobi_add_petersson_eq_zero
      D c hdeg F χ f hF hχ hunit hcusp hord hf0
  refine ⟨F, χ, f, hF, hχ, hunit, hcusp, hord, hrec, 0, Submodule.zero_mem _, fun g => ?_⟩
  rw [hf0 g, LinearMap.zero_apply]

end Main

end ModularCurve.AbelReciprocityThirdKind

open scoped MatrixGroups Topology in
open UpperHalfPlane MeasureTheory ModularCurve.AbelReciprocityThirdKind in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ)) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N,
        χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ f).re : ℂ))) ∧
      ∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g :=
  main D c hdeg

end S_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice (solution)
