-- Prove2me | solution 1 for ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/228ce1d3-c329-5157-9cdd-8cb5d65015e2

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CuspSpace
import Theorems.Thm_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four
import Theorems.Thm_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo
import Theorems.Thm_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount
import Theorems.Thm_CuspForm_genusFormula_le_finrank_gamma0_weight_two
import Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_period
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_period_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

open scoped MatrixGroups
open CongruenceSubgroup

namespace KbUnitaryCharExp

theorem mul_self_eq_trace_smul_sub_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    M * M = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.trace_fin_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp; linear_combination (-1 : ℤ) * hdet
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero]; ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero]; ring
  · simp; linear_combination (-1 : ℤ) * hdet

theorem pow_twelve_eq_one (γ : SL(2, ℤ)) (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 < 4) :
    γ ^ 12 = 1 := by
  have hM := mul_self_eq_trace_smul_sub_one (γ : Matrix (Fin 2) (Fin 2) ℤ) γ.det_coe
  generalize ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = t at h hM
  have h1 : t < 2 := by nlinarith
  have h2 : -2 < t := by nlinarith
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  set M := (γ : Matrix (Fin 2) (Fin 2) ℤ)
  interval_cases t
  · have h3 : M ^ 3 = 1 := by
      rw [pow_succ, sq, hM]; simp only [neg_smul, one_smul, Int.reduceNeg]
      rw [sub_mul, neg_mul, hM]; simp
    rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, h3, one_pow]
  · have h4 : M ^ 2 = -1 := by rw [sq, hM]; simp
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, h4]; norm_num
  · have h3 : M ^ 3 = -1 := by
      rw [pow_succ, sq, hM]; simp only [one_smul]
      rw [sub_mul, hM]; simp
    rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, h3]; norm_num

variable (N : ℕ)

def Ell : Set (Gamma0 N) := {γ | ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4}

def Msub : Subgroup (Abelianization (Gamma0 N)) :=
  Subgroup.closure (Abelianization.of '' Ell N)

abbrev Qm := Abelianization (Gamma0 N) ⧸ Msub N

abbrev Q := Additive (Qm N)

def piM : Gamma0 N →* Qm N := (QuotientGroup.mk' (Msub N)).comp Abelianization.of

def piA : Additive (Gamma0 N) →+ Q N := MonoidHom.toAdditive (piM N)

theorem piM_surjective : Function.Surjective (piM N) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    induction a using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩

theorem piA_surjective : Function.Surjective (piA N) := fun q =>
  let ⟨g, hg⟩ := piM_surjective N (Additive.toMul q); ⟨Additive.ofMul g, hg⟩

theorem piM_eq_one {γ : Gamma0 N} (hγ : γ ∈ Ell N) : piM N γ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨γ, hγ, rfl⟩)

theorem piA_apply (γ : Gamma0 N) : piA N (Additive.ofMul γ) = Additive.ofMul (piM N γ) := rfl

theorem piA_eq_zero {γ : Gamma0 N} (hγ : γ ∈ Ell N) : piA N (Additive.ofMul γ) = 0 := by
  rw [piA_apply, piM_eq_one N hγ]; rfl

variable {N} in

def desc {A : Type*} [CommGroup A] (f : Gamma0 N →* A) (hf : ∀ γ ∈ Ell N, f γ = 1) : Qm N →* A :=
  QuotientGroup.lift (Msub N) (Abelianization.lift f) ((Subgroup.closure_le _).mpr (by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Abelianization.lift_apply_of, hf γ hγ]))

theorem desc_piM {A : Type*} [CommGroup A] (f : Gamma0 N →* A) (hf : ∀ γ ∈ Ell N, f γ = 1)
    (γ : Gamma0 N) : desc f hf (piM N γ) = f γ := rfl

variable {N} in

def descA {A : Type*} [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A)
    (hφ : ∀ γ ∈ Ell N, φ (Additive.ofMul γ) = 0) : Q N →+ A :=
  MonoidHom.toAdditiveLeft (desc (AddMonoidHom.toMultiplicativeRight φ) hφ)

theorem descA_piA {A : Type*} [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A)
    (hφ : ∀ γ ∈ Ell N, φ (Additive.ofMul γ) = 0) (γ : Gamma0 N) :
    descA φ hφ (piA N (Additive.ofMul γ)) = φ (Additive.ofMul γ) := rfl

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    _root_.SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance fgQ [NeZero N] : AddGroup.FG (Q N) := by
  haveI := fg_SL2Z
  haveI : Group.FG (Gamma0 N) := inferInstance
  haveI : Group.FG (Qm N) := Group.fg_of_surjective (piM_surjective N)
  infer_instance

theorem apply_eq_zero_of_nsmul_eq_zero {A : Type*} [AddGroup A] (ψ : A →+ ℝ) {x : A} {m : ℕ}
    (hm : m ≠ 0) (hx : m • x = 0) : ψ x = 0 := by
  have h : (m : ℝ) * ψ x = 0 := by rw [← nsmul_eq_mul, ← map_nsmul, hx, map_zero]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hm)
  · exact h

section Decomp

variable {N} [NeZero N]
variable {n : ℕ} {ι : Type} [Fintype ι] {p e : ι → ℕ}
  (eqv : Q N ≃+ (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i)))

omit [NeZero N] [Fintype ι] in

theorem hom_ext_of_basis {A : Type*} [AddCommGroup A] (ψ₁ ψ₂ : Q N →+ A)
    (hb : ∀ j, ψ₁ (eqv.symm (Finsupp.single j 1, 0)) = ψ₂ (eqv.symm (Finsupp.single j 1, 0)))
    (ht : ∀ t, ψ₁ (eqv.symm (0, t)) = ψ₂ (eqv.symm (0, t))) : ψ₁ = ψ₂ := by
  have hfree : ψ₁.comp (eqv.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)) =
      ψ₂.comp (eqv.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)) := by
    refine Finsupp.addHom_ext' fun j => AddMonoidHom.ext_int ?_
    simpa using hb j
  refine AddMonoidHom.ext fun q => ?_
  obtain ⟨⟨v, t⟩, rfl⟩ := eqv.symm.surjective q
  have hsplit : ((v, t) : (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i))) =
      (v, 0) + (0, t) := by simp
  rw [hsplit, map_add, map_add, map_add, ht t]
  congr 1
  exact DFunLike.congr_fun hfree v

omit [NeZero N] in

theorem realChar_eq_zero (hp : ∀ i, (p i).Prime) (ψ : Q N →+ ℝ)
    (hψ : ∀ j, ψ (eqv.symm (Finsupp.single j 1, 0)) = 0) : ψ = 0 := by
  classical
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  refine hom_ext_of_basis eqv ψ 0 (by simpa using hψ) fun t => ?_
  obtain ⟨m, hm, hmt⟩ := (isOfFinAddOrder_of_finite t).exists_nsmul_eq_zero
  rw [AddMonoidHom.zero_apply]
  refine apply_eq_zero_of_nsmul_eq_zero _ hm.ne' ?_
  rw [← map_nsmul, Prod.smul_mk, smul_zero, hmt, Prod.mk_zero_zero, map_zero]

omit [Fintype ι] in
include eqv in

theorem card_succ_le_two_mul_genusFormula (i₀ : ι) (hp : (p i₀).Prime) (he : e i₀ ≠ 0) :
    ((n + 1 : ℕ) : ℚ) ≤ 2 * ModularCurve.genusFormula N := by
  classical
  haveI : Fact (p i₀).Prime := ⟨hp⟩

  let crd : Fin n → (Q N →+ ℤ) := fun j =>
    (Finsupp.applyAddHom j).comp ((AddMonoidHom.fst _ _).comp eqv.toAddMonoidHom)
  let tcrd : Q N →+ ZMod (p i₀ ^ e i₀) :=
    (DirectSum.component ℤ ι (fun i => ZMod (p i ^ e i)) i₀).toAddMonoidHom.comp
      ((AddMonoidHom.snd _ _).comp eqv.toAddMonoidHom)
  let Φn : Additive (Gamma0 N) →+ ZMod (p i₀) :=
    ((ZMod.castHom (dvd_pow_self (p i₀) he) (ZMod (p i₀))).toAddMonoidHom.comp tcrd).comp (piA N)
  let Φs : Fin n → (Additive (Gamma0 N) →+ ZMod (p i₀)) := fun j =>
    ((Int.castAddHom (ZMod (p i₀))).comp (crd j)).comp (piA N)
  let Φ : Option (Fin n) → (Additive (Gamma0 N) →+ ZMod (p i₀)) := fun o => o.elim Φn Φs
  have hΦ : ∀ (o : Option (Fin n)) (γ : Gamma0 N),
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → Φ o (Additive.ofMul γ) = 0 := by
    intro o γ hγ
    cases o <;> simp [Φ, Φn, Φs, piA_eq_zero N hγ]

  choose g hg using fun j : Fin n => piA_surjective N (eqv.symm (Finsupp.single j 1, 0))
  obtain ⟨g₀, hg₀⟩ :=
    piA_surjective N (eqv.symm (0, DirectSum.of (fun i => ZMod (p i ^ e i)) i₀ 1))
  have vss : ∀ j j', Φ (some j') (g j) = if j = j' then 1 else 0 := by
    intro j j'
    simp [Φ, Φs, crd, hg, Finsupp.single_apply]
  have vns : ∀ j, Φ none (g j) = 0 := by
    intro j
    simp [Φ, Φn, tcrd, hg]
  have vsn : ∀ j', Φ (some j') g₀ = 0 := by
    intro j'
    simp [Φ, Φs, crd, hg₀]
  have vnn : Φ none g₀ = 1 := by
    have htc : tcrd (piA N g₀) = 1 := by
      simp [tcrd, hg₀, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
    show (ZMod.castHom (dvd_pow_self (p i₀) he) (ZMod (p i₀))) (tcrd (piA N g₀)) = 1
    rw [htc, map_one]
  have hli : LinearIndependent (ZMod (p i₀)) Φ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hev : ∀ x, ∑ o, c o * Φ o x = 0 := fun x => by
      simpa using congrArg (fun ψ : Additive (Gamma0 N) →+ ZMod (p i₀) => ψ x) hc
    have hnone : c none = 0 := by simpa [Fintype.sum_option, vnn, vsn] using hev g₀
    rintro (_ | j)
    · exact hnone
    · simpa [Fintype.sum_option, vns, vss] using hev (g j)
  have hE := ModularCurve.six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four N
    (ZMod (p i₀)) Φ hli hΦ
  rw [Fintype.card_option, Fintype.card_fin,
    ModularCurve.natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo N,
    ModularCurve.natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree N,
    ModularCurve.Gamma0_index N,
    ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount (NeZero.ne N)] at hE
  have hQ : (6 * (n + 1) + 6 * ModularCurve.cuspCount N + 3 * ModularCurve.nuTwo N
      + 4 * ModularCurve.nuThree N : ℚ) ≤ 12 + ModularCurve.dedekindPsi N := by
    exact_mod_cast hE
  unfold ModularCurve.genusFormula
  push_cast
  linarith

omit [Fintype ι] in
include eqv in

theorem two_mul_finrank_le [Fintype ι] (hp : ∀ i, (p i).Prime) :
    2 * Module.finrank ℂ (CuspForm (Gamma0 N) 2) ≤ n := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank ℂ (CuspForm (Gamma0 N) 2) = d := ⟨_, rfl⟩
  rw [hd]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]; exact Nat.zero_le _
  haveI : Module.Finite ℂ (CuspForm (Gamma0 N) 2) := Module.finite_of_finrank_pos (hd ▸ hdpos)
  let b := Module.finBasisOfFinrankEq ℂ (CuspForm (Gamma0 N) 2) hd
  choose g hg using fun j : Fin n => piA_surjective N (eqv.symm (Finsupp.single j 1, 0))
  obtain ⟨Φd, hpar, hΦd⟩ := ModularCurve.exists_isParabolicHom_apply_eq_period N

  have key : ∀ f : CuspForm (Gamma0 N) 2,
      (∀ j, (ModularCurve.period N (Additive.toMul (g j)) f).re = 0) → f = 0 := by
    intro f hf
    let φf : Additive (Gamma0 N) →+ ℝ :=
      { toFun := fun x => (Φd x f).re
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hkill : ∀ γ ∈ Ell N, φf (Additive.ofMul γ) = 0 := by
      intro γ hγ
      rcases (show ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 from hγ).lt_or_eq with
        hlt | heq
      · have h12 : γ ^ 12 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_twelve_eq_one _ hlt)
        refine apply_eq_zero_of_nsmul_eq_zero φf (m := 12) (by norm_num) ?_
        rw [← ofMul_pow, h12, ofMul_one]
      · show (Φd (Additive.ofMul γ) f).re = 0
        rw [hpar γ heq, LinearMap.zero_apply, Complex.zero_re]
    have hψ : descA φf hkill = 0 := by
      refine realChar_eq_zero eqv hp _ fun j => ?_
      rw [← hg j]
      change descA φf hkill (piA N (Additive.ofMul (Additive.toMul (g j)))) = 0
      rw [descA_piA]
      show (Φd (Additive.ofMul (Additive.toMul (g j))) f).re = 0
      rw [hΦd]
      exact hf j
    refine ModularCurve.eq_zero_of_forall_re_period_eq_zero N f fun γ => ?_
    have h := DFunLike.congr_fun hψ (piA N (Additive.ofMul γ))
    rw [descA_piA, AddMonoidHom.zero_apply] at h
    change (Φd (Additive.ofMul γ) f).re = 0 at h
    rwa [hΦd] at h

  let L : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun v j => (ModularCurve.period N (Additive.toMul (g j)) (b.equivFun.symm v)).re
      map_add' := fun v w => by
        funext j
        simp only [Pi.add_apply, map_add, Complex.add_re]
      map_smul' := fun r v => by
        funext j
        have hrv : r • v = (r : ℂ) • v := by funext k; simp [Complex.real_smul]
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [hrv, map_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul] }
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun v hv => ?_
    have hf : b.equivFun.symm v = 0 := key _ fun j => congr_fun hv j
    exact b.equivFun.symm.injective (by rw [hf, map_zero])
  have h1 := LinearMap.finrank_le_finrank_of_injective hL
  rw [Module.finrank_pi ℝ, Fintype.card_fin, Module.finrank_pi_fintype ℝ,
    Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h1
  omega

end Decomp

def unitChar (χ : Gamma0 N → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) : Gamma0 N →* Circle where
  toFun γ := ⟨χ γ, mem_sphere_zero_iff_norm.2 (hunit γ)⟩
  map_one' := Circle.ext (by
    have h1 : χ 1 ≠ 0 := fun h => by simpa [h] using hunit 1
    have h2 : χ 1 * χ 1 = χ 1 * 1 := by rw [mul_one, ← hmul, one_mul]
    rw [Circle.coe_one]
    exact (mul_right_inj' h1).mp h2)
  map_mul' γ δ := Circle.ext (by rw [Circle.coe_mul]; exact hmul γ δ)

theorem unitChar_apply (χ : Gamma0 N → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) (γ : Gamma0 N) : (unitChar N χ hmul hunit γ : ℂ) = χ γ := rfl

theorem main [NeZero N] (χ : Gamma0 N → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Gamma0 N,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive (Gamma0 N) →+ ℝ,
      (∀ γ : Gamma0 N, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 →
        φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Q N)

  have he : ∀ i, e i = 0 := by
    by_contra hne
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
    have hup := card_succ_le_two_mul_genusFormula eqv i₀ (hp i₀) hi₀
    have hlow := two_mul_finrank_le eqv hp
    have hRR := CuspForm.genusFormula_le_finrank_gamma0_weight_two N
    have hlow' : ((2 * Module.finrank ℂ (CuspForm (Gamma0 N) 2) : ℕ) : ℚ) ≤ n := by
      exact_mod_cast hlow
    push_cast at hlow' hup
    linarith
  have hsub : ∀ i, Subsingleton (ZMod (p i ^ e i)) := fun i =>
    ZMod.subsingleton_iff.mpr (by rw [he i, pow_zero])
  have htors : ∀ t : DirectSum ι (fun i => ZMod (p i ^ e i)), t = 0 := fun t =>
    DFinsupp.ext fun i => Subsingleton.elim _ _

  set χc := unitChar N χ hmul hunit with hχc_def
  have hχc : ∀ γ ∈ Ell N, χc γ = 1 := fun γ hγ =>
    Circle.ext (by rw [unitChar_apply, Circle.coe_one]; exact htriv γ hγ)
  let χQ : Q N →+ Additive Circle := MonoidHom.toAdditive (desc χc hχc)

  choose θ hθ using fun j : Fin n =>
    Circle.exp_surjective (Additive.toMul (χQ (eqv.symm (Finsupp.single j 1, 0))))
  let ψ : Q N →+ ℝ :=
    { toFun := fun q => ∑ j, ((eqv q).1 j : ℝ) * θ j
      map_zero' := by simp
      map_add' := fun a b => by simp [Finset.sum_add_distrib, add_mul] }
  have hψb : ∀ j, ψ (eqv.symm (Finsupp.single j 1, 0)) = θ j := by
    intro j
    simp [ψ, Finsupp.single_apply]
  have hfactor : χQ = Circle.expHom.comp ψ := by
    refine hom_ext_of_basis eqv _ _ (fun j => ?_) (fun t => ?_)
    · rw [AddMonoidHom.comp_apply, hψb, Circle.expHom_apply, Function.comp_apply, hθ]
      rfl
    · rw [htors t, Prod.mk_zero_zero, map_zero, map_zero, map_zero]
  refine ⟨(AddMonoidHom.mulLeft (1 / (2 * Real.pi))).comp (ψ.comp (piA N)), fun γ hγ => ?_,
    fun γ => ?_⟩
  · simp [piA_eq_zero N hγ]
  · have h1 : χ γ = ((desc χc hχc (piM N γ) : Circle) : ℂ) := rfl
    have h2 : desc χc hχc (piM N γ) = Circle.exp (ψ (piA N (Additive.ofMul γ))) := by
      have h := DFunLike.congr_fun hfactor (piA N (Additive.ofMul γ))
      exact Additive.ofMul.injective h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [h1, h2, Circle.coe_exp]
    congr 1
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
    push_cast
    field_simp

end KbUnitaryCharExp
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four.KbUnitaryCharExp"

theorem solution (N : ℕ) [NeZero N] (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ) (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : CongruenceSubgroup.Gamma0 N,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℝ,
      (∀ γ : CongruenceSubgroup.Gamma0 N,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) :=
  KbUnitaryCharExp.main N χ hmul hunit htriv

end S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four
end P2MW
export P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four (solution)
