-- Prove2me | solution 1 for ModularCurve.petersson_mem_periodLattice_iff_re_period_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7ca10cac-5b78-50b6-8cb6-65d04dd9e9df

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
import Theorems.Thm_ModularCurve_sum_period_mul_edgeIntegral_eq_zero
import Theorems.Thm_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
import Theorems.Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
import Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_period_eq_zero
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm
import Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_period
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_petersson_mem_periodLattice_iff_re_period_int
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

open scoped MatrixGroups ComplexConjugate
open UpperHalfPlane MeasureTheory

namespace ModularCurve
p2m_export "ModularCurve" "period periodLattice integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral sum_period_mul_edgeIntegral_eq_zero exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period exists_cuspForm_petersson_eq eq_zero_of_forall_re_period_eq_zero finrank_parabolicHoms_le_two_mul_finrank_cuspForm exists_isParabolicHom_apply_eq_period"
namespace RiemannFormIntegrality
p2m_open "ModularCurve"

open ModularCurve.Period

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

theorem period_mul_and_parabolic :
    (∀ γ δ : Γ, ModularCurve.period N (γ * δ) = ModularCurve.period N γ + ModularCurve.period N δ) ∧
      ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
        ModularCurve.period N γ = 0 := by
  obtain ⟨Φ, hΦpar, hΦ⟩ := ModularCurve.exists_isParabolicHom_apply_eq_period N
  refine ⟨fun γ δ => ?_, fun γ hγ => ?_⟩
  · rw [← hΦ, ← hΦ, ← hΦ, ofMul_mul, map_add]
  · rw [← hΦ]; exact hΦpar γ hγ

end RealES

section Tiling

variable (N : ℕ) [NeZero N]

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "Q" => SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
local notation "V" => CuspForm (CongruenceSubgroup.Gamma0 N) 2

@[reducible] noncomputable def fintypeQ : Fintype Q := Subgroup.fintypeQuotientOfFiniteIndex

attribute [local instance] fintypeQ

omit [NeZero N] in
theorem pair_mem (a : SL(2, ℤ)) (q : Q) : (Quotient.out (a • q))⁻¹ * a * Quotient.out q ∈ Γ := by
  have h : (QuotientGroup.mk (Quotient.out (a • q)) : Q) = QuotientGroup.mk (a * Quotient.out q) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

noncomputable def gT (q : Q) : Γ :=
  ⟨(Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q, pair_mem N _ q⟩

noncomputable def gS (q : Q) : Γ :=
  ⟨(Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q, pair_mem N _ q⟩

omit [NeZero N] in
theorem gT_coe (q : Q) : ((gT N q : Γ) : SL(2, ℤ)) =
    (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q := rfl

omit [NeZero N] in
theorem gS_coe (q : Q) : ((gS N q : Γ) : SL(2, ℤ)) =
    (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q := rfl

noncomputable def Gp (g : V) (q : Q) (z : ℂ) : ℂ :=
  g ((Quotient.out q)⁻¹ • ofComplex z) /
    denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2

omit [NeZero N] in
theorem Gp_spec (g : V) : ∀ (q : Q) (z : ℂ), Gp N g q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
    denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2 := fun _ _ => rfl

noncomputable def ray (g : V) (q : Q) : ℂ :=
  ∫ y in Set.Ioi (Real.sqrt 3 / 2), Gp N g q (-(1 / 2) + y * Complex.I)

noncomputable def arc (g : V) (q : Q) : ℂ :=
  ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
    Gp N g q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))

noncomputable def pet (k g : V) : ℂ :=
  ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N),
    UpperHalfPlane.petersson 2 k g τ

noncomputable def PD (c d : Q → ℂ) (g : V) : ℂ :=
  Complex.I * ∑ q : Q, c q * ray N g q + 1 / 2 * ∑ q : Q, d q * arc N g q

theorem PD_add (c d c' d' : Q → ℂ) (g : V) :
    PD N (c + c') (d + d') g = PD N c d g + PD N c' d' g := by
  simp only [PD, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem PD_zero (g : V) : PD N 0 0 g = 0 := by
  simp [PD]

theorem PD_neg (c d : Q → ℂ) (g : V) : PD N (-c) (-d) g = -PD N c d g := by
  simp only [PD, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem PD_congr {c d c' d' : Q → ℂ} (hc : ∀ q, c q = c' q) (hd : ∀ q, d q = d' q) (g : V) :
    PD N c d g = PD N c' d' g := by
  rw [show c = c' from funext hc, show d = d' from funext hd]

noncomputable def PDZ (φ : Additive Γ →+ ℤ) (g : V) : ℂ :=
  PD N (fun q => ((φ (Additive.ofMul (gT N q)) : ℤ) : ℂ))
    (fun q => ((φ (Additive.ofMul (gS N q)) : ℤ) : ℂ)) g

theorem PDZ_add (φ ψ : Additive Γ →+ ℤ) (g : V) : PDZ N (φ + ψ) g = PDZ N φ g + PDZ N ψ g := by
  rw [PDZ, PDZ, PDZ, ← PD_add]
  refine PD_congr N (fun q => ?_) (fun q => ?_) g <;> simp

theorem PDZ_zero (g : V) : PDZ N 0 g = 0 := by
  rw [PDZ, ← PD_zero N g]
  refine PD_congr N (fun q => ?_) (fun q => ?_) g <;> simp

theorem PDZ_neg (φ : Additive Γ →+ ℤ) (g : V) : PDZ N (-φ) g = -PDZ N φ g := by
  rw [PDZ, PDZ, ← PD_neg]
  refine PD_congr N (fun q => ?_) (fun q => ?_) g <;> simp

theorem sum_half_split (a b r : Q → ℂ) :
    ∑ q : Q, (a q + b q) / 2 * r q = 1 / 2 * ∑ q : Q, a q * r q + 1 / 2 * ∑ q : Q, b q * r q := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem bilRe (k g : V) :
    Complex.I * pet N k g =
      PD N (fun q => ((ModularCurve.period N (gT N q) k).re : ℂ))
        (fun q => ((ModularCurve.period N (gS N q) k).re : ℂ)) g := by
  have hB := ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
    k g (gT N) (gS N) (gT_coe N) (gS_coe N) (Gp N g) (Gp_spec N g)
  have hH := ModularCurve.sum_period_mul_edgeIntegral_eq_zero
    k g (gT N) (gS N) (gT_coe N) (gS_coe N) (Gp N g) (Gp_spec N g)
  simp only [PD, pet, ray, arc, Complex.re_eq_add_conj]
  rw [sum_half_split, sum_half_split]
  change Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
      (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) = _
  linear_combination hB - (1 / 2 : ℂ) * hH

theorem bilRe_int (k g : V) (φ : Additive Γ →+ ℤ)
    (hk : ∀ γ : Γ, (ModularCurve.period N γ k).re = ((φ (Additive.ofMul γ) : ℤ) : ℝ)) :
    Complex.I * pet N k g = PDZ N φ g := by
  rw [bilRe, PDZ]
  refine PD_congr N (fun q => ?_) (fun q => ?_) g
  · rw [hk]; norm_cast
  · rw [hk]; norm_cast

theorem measurableSet_gammaFundamentalSet :
    MeasurableSet (FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N)) :=
  MeasurableSet.iUnion fun q => (ModularGroup.isClosed_fd.smul (Quotient.out q)⁻¹).measurableSet

theorem pet_conj (k g : V) : pet N g k = conj (pet N k g) := by
  rw [pet, pet, ← integral_conj]
  refine setIntegral_congr_fun (measurableSet_gammaFundamentalSet N) fun τ _ => ?_
  simp only [UpperHalfPlane.petersson, map_mul, Complex.conj_conj, zpow_ofNat]
  rw [show conj (((τ : ℍ).im : ℂ) ^ 2) = ((τ : ℍ).im : ℂ) ^ 2 by
    rw [map_pow, Complex.conj_ofReal]]
  ring

theorem eq_of_pet_eq (k f : V) (h : ∀ g : V, pet N k g = pet N f g) : k = f := by
  haveI : FiniteDimensional ℂ V := CuspForm.finiteDimensional_Gamma0 N 2
  have h' : ∀ g : V, pet N g k = pet N g f := fun g => by
    rw [pet_conj, pet_conj N f, h g]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  obtain ⟨hℓ, hhℓ⟩ := ModularCurve.exists_cuspForm_petersson_eq ℓ
  rw [map_sub, ← hhℓ k, ← hhℓ f, sub_eq_zero]
  change Complex.I * pet N hℓ k = Complex.I * pet N hℓ f
  rw [h']

end Tiling

end ModularCurve.RiemannFormIntegrality

open ModularCurve.RiemannFormIntegrality ModularCurve.Period in
theorem solution
    {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    (∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g) ↔
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∃ m : ℤ, (ModularCurve.period N γ f).re = m := by
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := fintypeQ N
  obtain ⟨hmul, hpar⟩ := period_mul_and_parabolic N
  constructor
  ·
    rintro ⟨Λ, hΛ, hfΛ⟩

    have key : ∀ Λ ∈ ModularCurve.periodLattice N,
        ∃ φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
          IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ ∧
            ∀ g, PDZ N φ g = Λ g := by
      intro Λ hΛ
      induction hΛ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨δ, rfl⟩ := hx
        obtain ⟨φ, hφ, hφδ⟩ :=
          ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
            (gT N) (gS N) (gT_coe N) (gS_coe N) δ
        exact ⟨φ, hφ, fun g => hφδ g (Gp N g) (Gp_spec N g)⟩
      | zero => exact ⟨0, fun _ _ => rfl, fun g => by rw [PDZ_zero]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨φ, hφ, hφx⟩ := hx
        obtain ⟨ψ, hψ, hψy⟩ := hy
        refine ⟨φ + ψ, fun γ hγ => ?_, fun g => ?_⟩
        · rw [AddMonoidHom.add_apply, hφ γ hγ, hψ γ hγ, add_zero]
        · rw [PDZ_add, hφx, hψy]; rfl
      | smul n x _ hx =>
        obtain ⟨φ, hφ, hφx⟩ := hx
        refine ⟨n • φ, fun γ hγ => ?_, fun g => ?_⟩
        · rw [AddMonoidHom.smul_apply, hφ γ hγ, smul_zero]
        · rw [LinearMap.smul_apply]
          induction n using Int.induction_on with
          | zero => rw [zero_smul, zero_smul, PDZ_zero]
          | succ m ih => rw [add_smul, one_smul, PDZ_add, ih, add_smul, one_smul, hφx]
          | pred m ih =>
            rw [sub_smul, one_smul, sub_eq_add_neg, PDZ_add, PDZ_neg, ih, sub_smul, one_smul,
              hφx, sub_eq_add_neg]
    obtain ⟨φ, hφ, hφΛ⟩ := key Λ hΛ

    let φR : Additive (CongruenceSubgroup.Gamma0 N) →+ ℝ := (Int.castAddHom ℝ).comp φ
    have hφR : IsParabolicHom (CongruenceSubgroup.Gamma0 N) φR := fun γ hγ => by
      simp [φR, hφ γ hγ]
    obtain ⟨k, hk⟩ := exists_cuspForm_re_period_eq N φR hφR
    have hk' : ∀ γ, (ModularCurve.period N γ k).re = ((φ (Additive.ofMul γ) : ℤ) : ℝ) := fun γ => by
      rw [hk]; rfl

    have hkf : k = f := by
      refine eq_of_pet_eq N k f fun g => ?_
      have e1 := bilRe_int N k g φ hk'
      have e2 := hfΛ g
      rw [hφΛ] at e1
      change Complex.I * pet N f g = Λ g at e2
      exact mul_left_cancel₀ Complex.I_ne_zero (e1.trans e2.symm)
    intro γ
    exact ⟨φ (Additive.ofMul γ), by rw [← hkf, hk']⟩
  ·
    intro h
    choose m hm using h
    let φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ :=
      { toFun := fun x => m (Additive.toMul x)
        map_zero' := by
          have h1 : (ModularCurve.period N (1 : CongruenceSubgroup.Gamma0 N) f).re = 0 := by
            rw [hpar 1 (by simp), LinearMap.zero_apply, Complex.zero_re]
          have := hm 1
          rw [h1] at this
          change m 1 = 0
          exact_mod_cast this.symm
        map_add' := fun x y => by
          change m (Additive.toMul x * Additive.toMul y) = m (Additive.toMul x) + m (Additive.toMul y)
          have := hm (Additive.toMul x * Additive.toMul y)
          rw [hmul, LinearMap.add_apply, Complex.add_re, hm, hm] at this
          exact_mod_cast this.symm }
    have hφm : ∀ γ, φ (Additive.ofMul γ) = m γ := fun γ => rfl
    have hφ : IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ := fun γ hγ => by
      have := hm γ
      rw [hpar γ hγ, LinearMap.zero_apply, Complex.zero_re] at this
      rw [hφm]
      exact_mod_cast this.symm
    obtain ⟨Λ, hΛ, hΛφ⟩ :=
      ModularCurve.exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
        (gT N) (gS N) (gT_coe N) (gS_coe N) φ hφ
    refine ⟨Λ, hΛ, fun g => ?_⟩
    have e1 := bilRe_int N f g φ (fun γ => by rw [hφm, hm])
    have e2 := hΛφ g (Gp N g) (Gp_spec N g)
    change Complex.I * pet N f g = Λ g
    rw [e1, ← e2]
    rfl

end S_ModularCurve_petersson_mem_periodLattice_iff_re_period_int
end P2MW
export P2MW.S_ModularCurve_petersson_mem_periodLattice_iff_re_period_int (solution)
