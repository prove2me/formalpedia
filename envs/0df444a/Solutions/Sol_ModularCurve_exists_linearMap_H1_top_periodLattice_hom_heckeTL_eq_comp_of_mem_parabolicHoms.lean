-- Prove2me | solution 1 for ModularCurve.exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1a2f7ada-ac42-5bbf-b422-092c33235d08

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
import Theorems.Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_periodMap_heckeTLin
import Theorems.Thm_ModularCurve_periodMap_heckeULin
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
import Theorems.Thm_ModularCurve_PDPairing_heckeT0_apply_eq_heckeT_top_apply
import Theorems.Thm_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

noncomputable section

namespace C2

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.ModularCurve"

variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k] (N : ℕ) [NeZero N]

abbrev V : Type := CohCarrier.H1 N ⊤ 𝒪

abbrev Vpar : Submodule 𝒪 (V 𝒪 N) := Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪

abbrev Λ : Type := ↥(periodLattice N)

def red : (Λ N →+ 𝒪) →ₗ[𝒪] (Λ N →+ k) where
  toFun f := (algebraMap 𝒪 k : 𝒪 →+ k).comp f
  map_add' f g := by ext x; simp
  map_smul' r f := by ext x; simp [Algebra.smul_def]

@[scoped simp] theorem red_apply (f : Λ N →+ 𝒪) (x : Λ N) : red 𝒪 k N f x = algebraMap 𝒪 k (f x) := rfl

structure Seam where
  Ψ : ↥(Vpar 𝒪 N) ≃ₗ[𝒪] (Λ N →+ 𝒪)
  π : V 𝒪 N →ₗ[𝒪] ↥(Vpar 𝒪 N)
  hπ : ∀ v : ↥(Vpar 𝒪 N), π (v : V 𝒪 N) = v

def Seam.Φ (S : Seam 𝒪 N) : V 𝒪 N →ₗ[𝒪] (Λ N →+ k) :=
  (red 𝒪 k N) ∘ₗ S.Ψ.toLinearMap ∘ₗ S.π

theorem Seam.Φ_apply_of_mem (S : Seam 𝒪 N) {v : V 𝒪 N} (hv : v ∈ Vpar 𝒪 N) :
    S.Φ 𝒪 k N v = red 𝒪 k N (S.Ψ ⟨v, hv⟩) := by
  simp only [Seam.Φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show S.π v = ⟨v, hv⟩ from S.hπ ⟨v, hv⟩]

end C2
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.ModularCurve TensorProduct CongruenceSubgroup"
open scoped MatrixGroups

namespace C2

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (N : ℕ) [NeZero N]

abbrev P : Type := ↥(Period.parabolicHoms ℤ (Gamma0 N) ℤ)

scoped instance : IsAddTorsionFree 𝒪 := inferInstance

def ιData := (CohCarrier.exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top N 𝒪)

def ι : 𝒪 ⊗[ℤ] P N →ₗ[𝒪] V 𝒪 N := (ιData 𝒪 N).choose

theorem ι_tmul_apply (r : 𝒪) (x : P N) (γ : ↥(CohCarrier.GammaH N ⊤)) :
    ι 𝒪 N (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
      r * ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) : 𝒪) :=
  (ιData 𝒪 N).choose_spec.1 r x γ

theorem ι_injective : Function.Injective (ι 𝒪 N) := (ιData 𝒪 N).choose_spec.2.1

theorem range_ι : LinearMap.range (ι 𝒪 N) = Vpar 𝒪 N := (ιData 𝒪 N).choose_spec.2.2.1

theorem heckeT_ι (ℓ : ℕ) [NeZero ℓ] (r : 𝒪) (x y : P N)
    (h : (y : Additive ↥(Gamma0 N) →+ ℤ) = PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ)) :
    ι 𝒪 N (r ⊗ₜ[ℤ] y) = CohCarrier.heckeT N ⊤ ℓ 𝒪 (ι 𝒪 N (r ⊗ₜ[ℤ] x)) :=
  (ιData 𝒪 N).choose_spec.2.2.2 ℓ r x y h

def eVpar : ↥(Vpar 𝒪 N) ≃ₗ[𝒪] 𝒪 ⊗[ℤ] P N :=
  ((LinearEquiv.ofInjective (ι 𝒪 N) (ι_injective 𝒪 N)).trans (LinearEquiv.ofEq _ _ (range_ι 𝒪 N))).symm

theorem eVpar_symm_apply (z : 𝒪 ⊗[ℤ] P N) : ((eVpar 𝒪 N).symm z : V 𝒪 N) = ι 𝒪 N z := rfl

def EV : P N ≃ₗ[ℤ] Module.Dual ℤ (Λ N) :=
  (exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period N).choose

theorem EV_period (ψ : P N) (δ : Gamma0 N) :
    EV N ψ ⟨period N δ, period_mem_periodLattice N δ⟩ = (ψ : Additive (Gamma0 N) →+ ℤ) (Additive.ofMul δ) :=
  (exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period N).choose_spec ψ δ

def nΛ : ℕ := (exists_basis_periodLattice_linearIndependent_real_span_eq_top N).choose
def bΛ : Module.Basis (Fin (nΛ N)) ℤ (Λ N) :=
  (exists_basis_periodLattice_linearIndependent_real_span_eq_top N).choose_spec.choose

def eDual : 𝒪 ⊗[ℤ] Module.Dual ℤ (Λ N) ≃ₗ[𝒪] (Λ N →+ 𝒪) :=
  ((Algebra.TensorProduct.basis 𝒪 (bΛ N).dualBasis).repr.trans
    (Finsupp.linearEquivFunOnFinite 𝒪 𝒪 (Fin (nΛ N)))).trans
    (((bΛ N).constr 𝒪).trans (addMonoidHomLequivInt (A := Λ N) (B := 𝒪) 𝒪).symm)

private def _root_.C2.Ψ : ↥(Vpar 𝒪 N) ≃ₗ[𝒪] (Λ N →+ 𝒪) :=
  (eVpar 𝒪 N).trans (((EV N).baseChange ℤ 𝒪 _ _).trans (eDual 𝒪 N))

p2m_export "C2" "Ψ"

theorem eDual_tmul_apply (r : 𝒪) (f : Module.Dual ℤ (Λ N)) (lam : Λ N) :
    eDual 𝒪 N (r ⊗ₜ[ℤ] f) lam = r * ((f lam : ℤ) : 𝒪) := by
  simp only [eDual, LinearEquiv.trans_apply]
  rw [Algebra.TensorProduct.basis_repr_tmul]

  have hcoord : (Finsupp.linearEquivFunOnFinite 𝒪 𝒪 (Fin (nΛ N)))
      (r • Finsupp.mapRange (algebraMap ℤ 𝒪) (map_zero _) ((bΛ N).dualBasis.repr f)) =
      fun i => r * ((f (bΛ N i) : ℤ) : 𝒪) := by
    funext i
    simp [Module.Basis.dualBasis_repr]
  rw [hcoord]

  change ((bΛ N).constr 𝒪 (fun i => r * ((f (bΛ N i) : ℤ) : 𝒪))) lam = _
  rw [Module.Basis.constr_apply]

  have hf : ((f lam : ℤ) : 𝒪) = ∑ i, ((bΛ N).repr lam i : 𝒪) * ((f (bΛ N i) : ℤ) : 𝒪) := by
    conv_lhs => rw [← (bΛ N).sum_repr lam]
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    push_cast
    ring
  rw [hf, Finset.mul_sum, Finsupp.sum_fintype _ _ (fun i => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul]
  ring

theorem Ψ_symm_tmul_apply (r : 𝒪) (x : P N) (lam : Λ N) :
    Ψ 𝒪 N ((eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] x)) lam = r * ((EV N x lam : ℤ) : 𝒪) := by
  simp only [Ψ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.baseChange_tmul, eDual_tmul_apply]

theorem Ψ_symm_tmul_period (r : 𝒪) (x : P N) (δ : Gamma0 N) :
    Ψ 𝒪 N ((eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] x)) ⟨period N δ, period_mem_periodLattice N δ⟩ =
      r * (((x : Additive (Gamma0 N) →+ ℤ) (Additive.ofMul δ) : ℤ) : 𝒪) := by
  rw [Ψ_symm_tmul_apply, EV_period]

theorem exists_retraction [IsPrincipalIdealRing 𝒪] :
    ∃ π : V 𝒪 N →ₗ[𝒪] ↥(Vpar 𝒪 N), ∀ v : ↥(Vpar 𝒪 N), π (v : V 𝒪 N) = v := by

  haveI htf : NoZeroSMulDivisors 𝒪 (V 𝒪 N ⧸ Vpar 𝒪 N) := by
    refine ⟨fun {c q} h => ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      by_cases hc : c = 0
      · exact Or.inl hc
      · refine Or.inr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
        intro γ hγ
        have := h γ hγ
        change c • v (Additive.ofMul γ) = 0 at this
        rw [smul_eq_mul, mul_eq_zero] at this
        exact this.resolve_left hc
  haveI : Module.Finite 𝒪 (V 𝒪 N) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  haveI : Module.Free 𝒪 (V 𝒪 N ⧸ Vpar 𝒪 N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Vpar 𝒪 N).mkQ (LinearMap.id)
    (Submodule.mkQ_surjective _)
  let p : V 𝒪 N →ₗ[𝒪] V 𝒪 N := LinearMap.id - s ∘ₗ (Vpar 𝒪 N).mkQ
  have hp : ∀ v, p v ∈ Vpar 𝒪 N := by
    intro v
    rw [← Submodule.ker_mkQ (Vpar 𝒪 N), LinearMap.mem_ker]
    have := LinearMap.congr_fun hs ((Vpar 𝒪 N).mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this, sub_self]
  refine ⟨LinearMap.codRestrict (Vpar 𝒪 N) p hp, fun v => ?_⟩
  apply Subtype.ext
  simp only [LinearMap.codRestrict_apply, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr v.2, map_zero, sub_zero]

def seam [IsPrincipalIdealRing 𝒪] : Seam 𝒪 N where
  Ψ := Ψ 𝒪 N
  π := (exists_retraction 𝒪 N).choose
  hπ := (exists_retraction 𝒪 N).choose_spec

end C2
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

set_option autoImplicit false

namespace C2

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.ModularCurve IsLocalRing"

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]

section Lattice

variable {L : Type} [AddCommGroup L]

private def toZ {A : Type} [AddCommGroup A] (f : L →+ A) : L →ₗ[ℤ] A := f.toIntLinearMap

theorem ker_algebraMap_eq_maximalIdeal (hk : Function.Surjective (algebraMap 𝒪 k)) :
    RingHom.ker (algebraMap 𝒪 k) = maximalIdeal 𝒪 :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap 𝒪 k) hk)

theorem red_surjective_of_basis (hk : Function.Surjective (algebraMap 𝒪 k)) {ι : Type} [Fintype ι]
    (N : ℕ) [NeZero N] (b : Module.Basis ι ℤ (Λ N)) :
    Function.Surjective (red 𝒪 k N) := by
  intro f
  classical

  choose g hg using fun i => hk (f (b i))
  let F : Λ N →ₗ[ℤ] 𝒪 := b.constr ℤ g
  refine ⟨F.toAddMonoidHom, ?_⟩

  have : (red 𝒪 k N F.toAddMonoidHom).toIntLinearMap = f.toIntLinearMap := by
    apply b.ext
    intro i
    show red 𝒪 k N F.toAddMonoidHom (b i) = f (b i)
    rw [red_apply]
    show algebraMap 𝒪 k (b.constr ℤ g (b i)) = f (b i)
    rw [Module.Basis.constr_basis, hg]
  exact AddMonoidHom.toIntLinearMap_injective this

theorem red_eq_zero_iff_of_basis (hk : Function.Surjective (algebraMap 𝒪 k)) {ι : Type} [Fintype ι]
    (N : ℕ) [NeZero N] (b : Module.Basis ι ℤ (Λ N)) (F : Λ N →+ 𝒪) :
    red 𝒪 k N F = 0 ↔ F ∈ (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 (Λ N →+ 𝒪)) := by
  classical
  have hker := ker_algebraMap_eq_maximalIdeal (𝒪 := 𝒪) (k := k) hk
  constructor
  · intro h

    have hval : ∀ x, F x ∈ maximalIdeal 𝒪 := by
      intro x
      rw [← hker, RingHom.mem_ker]
      have := DFunLike.congr_fun h x
      rwa [red_apply, AddMonoidHom.zero_apply] at this

    let δ : ι → (Λ N →+ 𝒪) := fun i => (Int.castAddHom 𝒪).comp (b.coord i).toAddMonoidHom
    have hF : F = ∑ i, F (b i) • δ i := by
      apply AddMonoidHom.toIntLinearMap_injective
      apply b.ext
      intro j
      show F (b j) = (∑ i, F (b i) • δ i) (b j)
      rw [AddMonoidHom.finsetSum_apply]
      simp only [δ, AddMonoidHom.smul_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        rw [Finsupp.single_eq_of_ne hij]
        simp
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hF]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hval (b i)) Submodule.mem_top
  · intro h
    ext x
    rw [red_apply, AddMonoidHom.zero_apply, ← RingHom.mem_ker, hker]

    refine Submodule.smul_induction_on (p := fun G : Λ N →+ 𝒪 => G x ∈ maximalIdeal 𝒪) h ?_ ?_
    · intro m hm G _
      show (m • G) x ∈ maximalIdeal 𝒪
      rw [AddMonoidHom.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hm
    · intro G H hG hH
      show (G + H) x ∈ maximalIdeal 𝒪
      rw [AddMonoidHom.add_apply]
      exact Ideal.add_mem _ hG hH

end Lattice
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

theorem Seam.map_Φ_eq_top (hk : Function.Surjective (algebraMap 𝒪 k)) (N : ℕ) [NeZero N]
    (S : Seam 𝒪 N) : (Vpar 𝒪 N).map (S.Φ 𝒪 k N) = ⊤ := by
  obtain ⟨n, b, -, -⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  rw [eq_top_iff]
  intro f _
  obtain ⟨F, hF⟩ := red_surjective_of_basis (𝒪 := 𝒪) (k := k) hk N b f
  obtain ⟨w, hw⟩ := S.Ψ.surjective F
  refine ⟨(w : V 𝒪 N), w.2, ?_⟩
  rw [Seam.Φ_apply_of_mem 𝒪 k N S w.2]
  have : (⟨(w : V 𝒪 N), w.2⟩ : ↥(Vpar 𝒪 N)) = w := Subtype.ext rfl
  rw [this, hw, hF]

theorem Seam.Φ_eq_zero_iff (hk : Function.Surjective (algebraMap 𝒪 k)) (N : ℕ) [NeZero N]
    (S : Seam 𝒪 N) (v : V 𝒪 N) (hv : v ∈ Vpar 𝒪 N) :
    S.Φ 𝒪 k N v = 0 ↔ v ∈ maximalIdeal 𝒪 • Vpar 𝒪 N := by
  obtain ⟨n, b, -, -⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  rw [Seam.Φ_apply_of_mem 𝒪 k N S hv, red_eq_zero_iff_of_basis (𝒪 := 𝒪) (k := k) hk N b]

  have h1 : S.Ψ ⟨v, hv⟩ ∈ (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 (Λ N →+ 𝒪)) ↔
      (⟨v, hv⟩ : ↥(Vpar 𝒪 N)) ∈ (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 ↥(Vpar 𝒪 N)) := by
    have hmap : (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 ↥(Vpar 𝒪 N)).map S.Ψ.toLinearMap =
        (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 (Λ N →+ 𝒪)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    rw [← hmap, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, hwv⟩
      have : w = ⟨v, hv⟩ := S.Ψ.injective hwv
      rwa [this] at hw
    · intro h
      exact ⟨_, h, rfl⟩
  have h2 : (⟨v, hv⟩ : ↥(Vpar 𝒪 N)) ∈ (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 ↥(Vpar 𝒪 N)) ↔
      v ∈ maximalIdeal 𝒪 • Vpar 𝒪 N := by
    have hmap : (maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 ↥(Vpar 𝒪 N)).map (Vpar 𝒪 N).subtype =
        maximalIdeal 𝒪 • Vpar 𝒪 N := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← hmap, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have : w = ⟨v, hv⟩ := Subtype.ext hwv
      rwa [this] at hw
  rw [h1, h2]

end C2
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsEquivariantPrimitive Period.IsParabolicHom Period.IsEquivariantPrimitive.periodHom_apply Period.parabolicHoms Period.mem_parabolicHoms_iff period periodLattice period_mem_periodLattice cuspHeckeGen_of_dvd cuspHeckeGen_of_not_dvd cuspHeckeRep cuspHeckeRep_heckeGen dualHeckeRep dualHeckeRep_apply_apply periodLatticeHeckeEnd coe_periodLatticeHeckeEnd_apply heckeGen PDPairing.heckeT0 exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period exists_basis_periodLattice_linearIndependent_real_span_eq_top periodMap periodMap_def periodMap_heckeTLin periodMap_heckeULin period_apply_eq_sub_of_hasEquivariantPrimitive exists_hasEquivariantPrimitive periodLatticeHeckeStable PDPairing.heckeT0_apply_eq_heckeT_top_apply"
p2m_open "ModularCurve"

variable (N : ℕ) [NeZero N]

theorem periodMap_apply_ofMul (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (γ : CongruenceSubgroup.Gamma0 N) :
    periodMap N f (Additive.ofMul γ) = period N γ f := by
  obtain ⟨F, hF⟩ := exists_hasEquivariantPrimitive N f
  obtain ⟨F₀, h₀, hpm⟩ := periodMap_def N f hF
  rw [hpm, Period.IsEquivariantPrimitive.periodHom_apply,
    period_apply_eq_sub_of_hasEquivariantPrimitive N f h₀ γ]
  rfl

theorem periodMap_cuspHeckeRep_heckeGen (ℓ : Nat.Primes) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    periodMap N (cuspHeckeRep N (heckeGen ℓ) f) = HeckeEis.heckeOperatorHom N ℓ ℂ (periodMap N f) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  rw [cuspHeckeRep_heckeGen]
  by_cases h : (ℓ : ℕ) ∣ N
  · rw [cuspHeckeGen_of_dvd N ℓ h]
    exact periodMap_heckeULin ℓ.2 h f
  · rw [cuspHeckeGen_of_not_dvd N ℓ h]
    exact periodMap_heckeTLin ℓ.2 h f

theorem dualHeckeRep_heckeGen_period (ℓ : Nat.Primes) (δ : CongruenceSubgroup.Gamma0 N) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    dualHeckeRep N (heckeGen ℓ) (period N δ) =
      ∑ q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
        period N (HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) δ q)) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  apply LinearMap.ext
  intro f
  rw [dualHeckeRep_apply_apply, LinearMap.sum_apply, ← periodMap_apply_ofMul, periodMap_cuspHeckeRep_heckeGen,
    HeckeEis.heckeOperatorHom_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [periodMap_apply_ofMul]

theorem periodLatticeHeckeEnd_heckeGen_period (ℓ : Nat.Primes) (δ : CongruenceSubgroup.Gamma0 N) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    periodLatticeHeckeEnd N (heckeGen ℓ) ⟨period N δ, period_mem_periodLattice N δ⟩ =
      ∑ q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
        (⟨period N (HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) δ q)),
          period_mem_periodLattice N _⟩ : periodLattice N) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  apply Subtype.ext
  rw [coe_periodLatticeHeckeEnd_apply (periodLatticeHeckeStable N), Submodule.coe_sum]
  exact dualHeckeRep_heckeGen_period N ℓ δ

theorem apply_periodLatticeHeckeEnd_heckeGen_period {A : Type*} [AddCommGroup A]
    (ℓ : Nat.Primes) (x : Additive (CongruenceSubgroup.Gamma0 N) →+ A) (E : periodLattice N →+ A)
    (hE : ∀ γ : CongruenceSubgroup.Gamma0 N, E ⟨period N γ, period_mem_periodLattice N γ⟩ = x (Additive.ofMul γ))
    (δ : CongruenceSubgroup.Gamma0 N) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    E (periodLatticeHeckeEnd N (heckeGen ℓ) ⟨period N δ, period_mem_periodLattice N δ⟩) =
      HeckeEis.heckeOperatorHom N ℓ A x (Additive.ofMul δ) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  rw [periodLatticeHeckeEnd_heckeGen_period N ℓ δ, map_sum, HeckeEis.heckeOperatorHom_apply]
  exact Finset.sum_congr rfl fun q _ => hE _

theorem apply_periodLatticeHeckeEnd_heckeGen_period_eq_heckeT0 {A : Type*} [AddCommGroup A]
    (ℓ : Nat.Primes) (x : Additive (CongruenceSubgroup.Gamma0 N) →+ A) (E : periodLattice N →+ A)
    (hE : ∀ γ : CongruenceSubgroup.Gamma0 N, E ⟨period N γ, period_mem_periodLattice N γ⟩ = x (Additive.ofMul γ))
    (δ : CongruenceSubgroup.Gamma0 N) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    E (periodLatticeHeckeEnd N (heckeGen ℓ) ⟨period N δ, period_mem_periodLattice N δ⟩) =
      PDPairing.heckeT0 N ℓ A x (Additive.ofMul δ) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  rw [apply_periodLatticeHeckeEnd_heckeGen_period N ℓ x E hE δ]

  let φ : CohCarrier.H1 N ⊤ A := x.comp (MonoidHom.toAdditive (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 ⊤)))
  have hφ : ∀ γ : ↥(CohCarrier.GammaH N ⊤), φ (Additive.ofMul γ) =
      x (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := fun γ => rfl
  let γ : ↥(CohCarrier.GammaH N ⊤) := ⟨(δ : SL(2, ℤ)), by rw [CohCarrier.GammaH_top]; exact δ.2⟩
  have hδ : (⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩ : CongruenceSubgroup.Gamma0 N) = δ :=
    Subtype.ext rfl
  rw [← hδ, PDPairing.heckeT0_apply_eq_heckeT_top_apply N ℓ A φ x hφ γ,
    CohCarrier.heckeT_top_apply_eq_heckeOperatorHom N ℓ A φ x hφ γ]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.ModularCurve TensorProduct CongruenceSubgroup"
open scoped MatrixGroups

namespace C2

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (N : ℕ) [NeZero N]

theorem heckeTL_mem_Vpar (ℓ : ℕ) (hℓ : ℓ.Prime) (v : V 𝒪 N) (hv : v ∈ Vpar 𝒪 N) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ v) ∈ Vpar 𝒪 N := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hv' : v ∈ Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) 𝒪 :=
    Period.mem_parabolicHoms_iff.mpr (Period.mem_parabolicHoms_iff.mp hv)
  rw [Period.mem_parabolicHoms_iff]
  by_cases hℓN : ℓ ∣ N
  · have h := CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH N ⊤ (∅ : Set ℕ) 𝒪 (.U ℓ hℓ hℓN) v hv'
    exact Period.mem_parabolicHoms_iff.mp h
  · have h := CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH N ⊤ (∅ : Set ℕ) 𝒪
      (.T ℓ hℓ (Set.notMem_empty ℓ) hℓN) v hv'
    exact Period.mem_parabolicHoms_iff.mp h

theorem heckeT0_isParabolicHom (ℓ : ℕ) (hℓ : ℓ.Prime) (x : P N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    Period.IsParabolicHom (Gamma0 N) (PDPairing.heckeT0 N ℓ ℤ (x : Additive (Gamma0 N) →+ ℤ)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro γ₀ hγ₀
  let φ : CohCarrier.H1 N ⊤ ℤ :=
    (x : Additive (Gamma0 N) →+ ℤ).comp (MonoidHom.toAdditive (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 ⊤)))
  have hφ : ∀ γ : ↥(CohCarrier.GammaH N ⊤), φ (Additive.ofMul γ) =
      (x : Additive (Gamma0 N) →+ ℤ) (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) :=
    fun γ => rfl
  have hγH : (γ₀ : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by rw [CohCarrier.GammaH_top]; exact γ₀.2
  let γ : ↥(CohCarrier.GammaH N ⊤) := ⟨γ₀, hγH⟩
  have hγeq : (⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩ : Gamma0 N) = γ₀ := Subtype.ext rfl
  have h1 := PDPairing.heckeT0_apply_eq_heckeT_top_apply N ℓ ℤ φ (x : Additive (Gamma0 N) →+ ℤ) hφ γ
  rw [hγeq] at h1
  rw [h1]

  have hφpar : φ ∈ Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ := by
    rw [Period.mem_parabolicHoms_iff]
    intro γ' hγ'
    rw [hφ γ']
    exact (Period.mem_parabolicHoms_iff.mp x.2) _ hγ'
  have hT := heckeTL_mem_Vpar ℤ N ℓ hℓ φ hφpar
  rw [Period.mem_parabolicHoms_iff] at hT
  have := hT γ hγ₀
  rwa [CohCarrier.heckeTL_apply] at this

variable [IsPrincipalIdealRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

theorem seam_hecke (ℓ : Nat.Primes) (v : V 𝒪 N) (hv : v ∈ Vpar 𝒪 N) :
    (seam 𝒪 N).Φ 𝒪 k N ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ) v) =
      ((seam 𝒪 N).Φ 𝒪 k N v).comp (periodLatticeHeckeEnd N (heckeGen ℓ)).toAddMonoidHom := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  have hvr : v ∈ LinearMap.range (ι 𝒪 N) := by rw [range_ι]; exact hv
  obtain ⟨z, rfl⟩ := hvr

  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    have hma : ι 𝒪 N a ∈ Vpar 𝒪 N := by rw [← range_ι]; exact LinearMap.mem_range_self _ _
    have hmb : ι 𝒪 N b ∈ Vpar 𝒪 N := by rw [← range_ι]; exact LinearMap.mem_range_self _ _
    rw [map_add, map_add, map_add, map_add, AddMonoidHom.add_comp, ha hma, hb hmb]
  | tmul r x =>

    let y : P N := ⟨PDPairing.heckeT0 N ℓ ℤ (x : Additive (Gamma0 N) →+ ℤ),
      Period.mem_parabolicHoms_iff.mpr (heckeT0_isParabolicHom N ℓ ℓ.2 x)⟩
    have hTι : CohCarrier.heckeTL N ⊤ 𝒪 ℓ (ι 𝒪 N (r ⊗ₜ[ℤ] x)) = ι 𝒪 N (r ⊗ₜ[ℤ] y) := by
      rw [CohCarrier.heckeTL_apply]; exact (heckeT_ι 𝒪 N ℓ r x y rfl).symm
    rw [hTι]
    have hmx : ι 𝒪 N (r ⊗ₜ[ℤ] x) ∈ Vpar 𝒪 N := by rw [← range_ι]; exact LinearMap.mem_range_self _ _
    have hmy : ι 𝒪 N (r ⊗ₜ[ℤ] y) ∈ Vpar 𝒪 N := by rw [← range_ι]; exact LinearMap.mem_range_self _ _
    rw [Seam.Φ_apply_of_mem 𝒪 k N (seam 𝒪 N) hmy, Seam.Φ_apply_of_mem 𝒪 k N (seam 𝒪 N) hmx]
    have ex : (⟨ι 𝒪 N (r ⊗ₜ[ℤ] x), hmx⟩ : ↥(Vpar 𝒪 N)) = (eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] x) := Subtype.ext rfl
    have ey : (⟨ι 𝒪 N (r ⊗ₜ[ℤ] y), hmy⟩ : ↥(Vpar 𝒪 N)) = (eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] y) := Subtype.ext rfl
    change red 𝒪 k N (Ψ 𝒪 N ⟨ι 𝒪 N (r ⊗ₜ[ℤ] y), hmy⟩) =
      (red 𝒪 k N (Ψ 𝒪 N ⟨ι 𝒪 N (r ⊗ₜ[ℤ] x), hmx⟩)).comp _
    rw [ex, ey]

    apply AddMonoidHom.ext
    rintro ⟨μ, hμ⟩
    suffices h : ∀ (hμ' : μ ∈ periodLattice N),
        red 𝒪 k N (Ψ 𝒪 N ((eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] y))) ⟨μ, hμ'⟩ =
          ((red 𝒪 k N (Ψ 𝒪 N ((eVpar 𝒪 N).symm (r ⊗ₜ[ℤ] x)))).comp
            (periodLatticeHeckeEnd N (heckeGen ℓ)).toAddMonoidHom) ⟨μ, hμ'⟩ from h hμ
    induction hμ using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨δ, rfl⟩ := hp
      intro hμ'
      rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, red_apply, red_apply,
        Ψ_symm_tmul_period, Ψ_symm_tmul_apply]
      congr 2
      have hE := apply_periodLatticeHeckeEnd_heckeGen_period_eq_heckeT0 N ℓ (x : Additive (Gamma0 N) →+ ℤ)
        (EV N x).toAddMonoidHom (fun γ => EV_period N x γ) δ
      exact (hE).symm ▸ rfl
    | zero => intro hμ'; simp [show (⟨0, hμ'⟩ : ↥(periodLattice N)) = 0 from rfl]
    | add a b ha hb iha ihb =>
      intro hμ'
      have := congrArg₂ (· + ·) (iha ha) (ihb hb)
      simp only [← map_add] at this
      convert this using 2 <;> rfl
    | smul n a ha iha =>
      intro hμ'
      have := congrArg (fun t => n • t) (iha ha)
      simp only [← map_zsmul] at this
      convert this using 2 <;> rfl

end C2
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (N : ℕ) [NeZero N] :
    ∃ Φ : CohCarrier.H1 N ⊤ 𝒪 →ₗ[𝒪] (↥(ModularCurve.periodLattice N) →+ k),
      (∀ (ℓ : Nat.Primes) (v : CohCarrier.H1 N ⊤ 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
          Φ ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ) v) =
            (Φ v).comp
              (ModularCurve.periodLatticeHeckeEnd N (ModularCurve.heckeGen ℓ)).toAddMonoidHom) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).map Φ = ⊤ ∧
      (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
          (Φ v = 0 ↔ v ∈ IsLocalRing.maximalIdeal 𝒪 •
            ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)) :=
  ⟨(C2.seam 𝒪 N).Φ 𝒪 k N, fun ℓ v hv => C2.seam_hecke 𝒪 N k ℓ v hv,
    C2.Seam.map_Φ_eq_top hk N (C2.seam 𝒪 N), fun v hv => C2.Seam.Φ_eq_zero_iff hk N (C2.seam 𝒪 N) v hv⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2"

end S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
end P2MW
export P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms (solution)
