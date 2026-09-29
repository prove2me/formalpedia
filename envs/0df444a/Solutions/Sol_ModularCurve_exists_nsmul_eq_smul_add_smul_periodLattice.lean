-- Prove2me | solution 1 for ModularCurve.exists_nsmul_eq_smul_add_smul_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/32099f03-e9c6-57c8-8711-f06c4ad06bb2

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
import Theorems.Thm_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
import Theorems.Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

noncomputable section

open Module
open scoped Matrix

namespace W1C

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def mulI : E →ₗ[ℝ] E := (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ

@[scoped simp] theorem mulI_apply (x : E) : mulI x = Complex.I • x := rfl

theorem mulI_injective : Function.Injective (mulI : E →ₗ[ℝ] E) := by
  intro x y h
  simp only [mulI_apply] at h
  have := congrArg (fun z => Complex.I • z) h
  simpa [smul_smul] using this

theorem complex_smul_eq (z : ℂ) (x : E) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem mem_sup_of_mem_span_complex (S : Set E) {x : E} (hx : x ∈ Submodule.span ℂ S) :
    x ∈ Submodule.span ℝ S ⊔ (Submodule.span ℝ S).map mulI := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    rw [smul_add, complex_smul_eq, complex_smul_eq c (mulI v')]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hu)
    · exact Submodule.mem_sup_right ⟨c.im • u, Submodule.smul_mem _ _ hu, by simp⟩
    · exact Submodule.mem_sup_right ⟨c.re • v', Submodule.smul_mem _ _ hv', by simp⟩
    · refine Submodule.mem_sup_left ?_
      have : c.im • (Complex.I • (mulI v' : E)) = (-c.im) • v' := by
        simp [smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hv'

theorem restrictScalars_span_complex (S : Set E) :
    (Submodule.span ℂ S).restrictScalars ℝ = Submodule.span ℝ S ⊔ (Submodule.span ℝ S).map mulI := by
  refine le_antisymm (fun x hx => mem_sup_of_mem_span_complex S hx) ?_
  refine sup_le ?_ ?_
  · exact (Submodule.span_le_restrictScalars ℝ ℂ S)
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span ℂ S := Submodule.span_le_restrictScalars ℝ ℂ S hy
    exact Submodule.smul_mem _ Complex.I hy'

end W1C
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C"

namespace W1A

open ModularCurve W1C

variable (N : ℕ) [NeZero N]

abbrev V : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2
abbrev D : Type := Module.Dual ℂ (V N)

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

def a1 : D N where
  toFun f := ModularFormClass.qCoeff (⇑f) 1
  map_add' f g := by
    simp only [ModularFormClass.qCoeff]
    rw [show (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g from rfl,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
  map_smul' c f := by
    simp only [ModularFormClass.qCoeff, RingHom.id_apply, smul_eq_mul]
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f]
    simp

@[scoped simp] theorem a1_apply (f : V N) : a1 N f = ModularFormClass.qCoeff (⇑f) 1 := rfl

def Θ : Module.End ℂ (V N) →ₗ[ℂ] D N where
  toFun S := (a1 N).comp S
  map_add' S S' := LinearMap.comp_add _ _ _
  map_smul' c S := LinearMap.comp_smul _ _ _

@[scoped simp] theorem Θ_apply (S : Module.End ℂ (V N)) (f : V N) : Θ N S f = a1 N (S f) := rfl

theorem Θ_eq_dualHeckeRep (t : HeckeAlg) : Θ N (cuspHeckeRep N t) = dualHeckeRep N t (a1 N) := rfl

abbrev C : Submodule ℂ (Module.End ℂ (V N)) :=
  Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (V N)))

theorem C_eq_span_range : C N = Submodule.span ℂ (Set.range (cuspHeckeRep N)) := by
  rw [range_cuspHeckeRep]

section Generation

variable
  (hB3a : ∀ T : Module.End ℂ (V N), T ∈ C N →
    (∀ f : V N, ModularFormClass.qCoeff (⇑(T f)) 1 = 0) → T = 0)
  (hB3c : finrank ℂ (C N) = finrank ℂ (V N))
  [FiniteDimensional ℂ (V N)]

include hB3a hB3c

theorem map_C_Θ_eq_top : (C N).map (Θ N) = ⊤ := by
  have hinj : Function.Injective ((Θ N).domRestrict (C N)) := by
    intro S S' h
    have h' : Θ N (S : Module.End ℂ (V N)) = Θ N S' := h
    have hd : Θ N ((S : Module.End ℂ (V N)) - S') = 0 := by rw [map_sub, h', sub_self]
    have h0 := hB3a ((S : Module.End ℂ (V N)) - S') (Submodule.sub_mem _ S.2 S'.2) (fun f => by
      have := congrArg (fun φ : D N => φ f) hd
      simpa only [Θ_apply, a1_apply, LinearMap.zero_apply] using this)
    exact Subtype.ext (sub_eq_zero.mp h0)
  apply Submodule.eq_top_of_finrank_eq
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj hinj, hB3c]
  exact (Subspace.dual_finrank_eq).symm

theorem span_range_dualHeckeRep_a1 :
    Submodule.span ℂ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) = ⊤ := by
  apply top_le_iff.mp
  rw [← map_C_Θ_eq_top N hB3a hB3c, C_eq_span_range, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨t, (Θ_eq_dualHeckeRep N t).symm⟩

def u : Fin 2 → D N := ![a1 N, Complex.I • a1 N]

theorem span_real_eq_top :
    Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) = ⊤ := by
  apply top_le_iff.mp
  intro δ _
  have hδ : δ ∈ Submodule.span ℂ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) := by
    rw [span_range_dualHeckeRep_a1 N hB3a hB3c]; trivial
  have h := mem_sup_of_mem_span_complex _ hδ
  set S := Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2))
  have h1 : Submodule.span ℝ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) ≤ S := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨(t, 0), by simp [u]⟩
  have h2 : (Submodule.span ℝ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N))).map mulI ≤ S := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨(t, 1), ?_⟩
    simp [u, map_smul]
  exact sup_le h1 h2 h

end Generation
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C"

section Lattice

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
  (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
  (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
  (hst : PeriodLatticeHeckeStable N)

def bℝ : Module.Basis (Fin n) ℝ (D N) := Module.Basis.mk hli hsp.ge

theorem bℝ_apply (i : Fin n) : bℝ N b hli hsp i = ((b i : periodLattice N) : D N) := by
  rw [bℝ, Module.Basis.mk_apply]

theorem bℝ_repr_coe (x : periodLattice N) (i : Fin n) :
    (bℝ N b hli hsp).repr (x : D N) i = (b.repr x i : ℝ) := by
  have hx : (x : D N) = ∑ j, ((b.repr x j : ℤ) : ℝ) • bℝ N b hli hsp j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, bℝ_apply, Int.cast_smul_eq_zsmul]
  rw [hx, (bℝ N b hli hsp).repr_sum_self]

def Mℤ : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp (periodLatticeHeckeEnd N)

theorem Mℤ_apply (t : HeckeAlg) : Mℤ N b t = LinearMap.toMatrix b b (periodLatticeHeckeEnd N t) := rfl

include hst in

theorem toMatrix_dualHeckeRep (t : HeckeAlg) :
    LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((dualHeckeRep N t).restrictScalars ℝ) =
      (Mℤ N b t).map (Int.cast : ℤ → ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.restrictScalars_apply, bℝ_apply,
    ← coe_periodLatticeHeckeEnd_apply hst, bℝ_repr_coe, Matrix.map_apply, Mℤ_apply,
    LinearMap.toMatrix_apply]

include hst in
theorem equivFun_dualHeckeRep (t : HeckeAlg) (δ : D N) :
    (bℝ N b hli hsp).equivFun (dualHeckeRep N t δ) =
      (Mℤ N b t).map (Int.cast : ℤ → ℝ) *ᵥ (bℝ N b hli hsp).equivFun δ := by
  have h := LinearMap.toMatrix_mulVec_repr (bℝ N b hli hsp) (bℝ N b hli hsp)
    ((dualHeckeRep N t).restrictScalars ℝ) δ
  rw [toMatrix_dualHeckeRep N b hli hsp hst] at h
  simp only [Module.Basis.equivFun_apply]
  exact h.symm

include hli hsp hst in

theorem exists_w
    (hgen : Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) = ⊤) :
    ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 =>
        (Mℤ N b ta.1).map (Int.cast : ℤ → ℝ) *ᵥ w ta.2) = ⊤ := by
  refine ⟨fun a => (bℝ N b hli hsp).equivFun (u N a), ?_⟩
  have : (Set.range fun ta : HeckeAlg × Fin 2 => (Mℤ N b ta.1).map (Int.cast : ℤ → ℝ) *ᵥ
      (bℝ N b hli hsp).equivFun (u N ta.2)) =
      (bℝ N b hli hsp).equivFun '' (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) := by
    rw [← Set.range_comp]
    congr 1
    funext ta
    simp only [Function.comp_apply]
    exact (equivFun_dualHeckeRep N b hli hsp hst ta.1 (u N ta.2)).symm
  rw [this]
  change Submodule.span ℝ (((bℝ N b hli hsp).equivFun : D N →ₗ[ℝ] (Fin n → ℝ)) '' _) = ⊤
  rw [Submodule.span_image, hgen, Submodule.map_top, LinearMap.range_eq_top]
  exact (bℝ N b hli hsp).equivFun.surjective

end Lattice
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C"

end W1A
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

namespace W1A

open ModularCurve W1C

variable (N : ℕ) [NeZero N]

section Dimension

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
  (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
  (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
  (hst : PeriodLatticeHeckeStable N)
  [FiniteDimensional ℂ (V N)]

theorem dualMap_injective' : Function.Injective
    (fun S : Module.End ℂ (V N) => (S.dualMap : Module.End ℂ (D N))) := by
  intro S S' h
  refine LinearMap.ext fun f => ?_
  have : ∀ φ : D N, φ (S f) = φ (S' f) := fun φ => by
    have := congrArg (fun T : Module.End ℂ (D N) => T φ f) h
    simpa using this
  have h0 : ∀ φ : D N, φ (S f - S' f) = 0 := fun φ => by rw [map_sub, this φ, sub_self]
  exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp h0)

def Ψ₁ : Module.End ℂ (V N) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun S := LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((S.dualMap).restrictScalars ℝ)
  map_add' S S' := by
    have : (S + S').dualMap = S.dualMap + S'.dualMap := map_add (Module.Dual.transpose (R := ℂ)) S S'
    rw [this, LinearMap.restrictScalars_add, map_add]
  map_smul' r S := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.restrictScalars_apply, LinearMap.dualMap_apply',
      RingHom.id_apply, Matrix.smul_apply, smul_eq_mul]
    have : (bℝ N b hli hsp j).comp (r • S) = r • ((bℝ N b hli hsp j).comp S) := by
      ext f; simp
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Ψ₁_injective : Function.Injective (Ψ₁ N b hli hsp) := by
  intro S S' h
  apply dualMap_injective' N
  have h' := (LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp)).injective h
  exact LinearMap.restrictScalars_injective ℝ h'

include hst in
theorem Ψ₁_cuspHeckeRep (t : HeckeAlg) :
    Ψ₁ N b hli hsp (cuspHeckeRep N t) = (Mℤ N b t).map (Int.cast : ℤ → ℝ) := by
  show LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((dualHeckeRep N t).restrictScalars ℝ) = _
  exact toMatrix_dualHeckeRep N b hli hsp hst t

abbrev RVℝ : Submodule ℝ (Module.End ℂ (V N)) := Submodule.span ℝ (Set.range (cuspHeckeRep N))

include hli hsp hst in
theorem finrank_span_MK_real_eq :
    finrank ℝ (Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ))) =
      finrank ℝ (RVℝ N) := by
  have hr : (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
      Set.range ((Ψ₁ N b hli hsp) ∘ (cuspHeckeRep N)) := by
    congr 1
    funext t
    exact (Ψ₁_cuspHeckeRep N b hli hsp hst t).symm
  have : Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
      (RVℝ N).map (Ψ₁ N b hli hsp) := by
    rw [hr, Set.range_comp, Submodule.map_span]
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Ψ₁ N b hli hsp)
    (Ψ₁_injective N b hli hsp) (RVℝ N))).symm

end Dimension
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

section Rational

variable {m : ℕ} (β : Module.Basis (Fin m) ℂ (V N))
  (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin m),
    β.repr (CuspForm.heckeTLin 2 hℓ hℓN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
  (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin m),
    β.repr (CuspForm.heckeULin 2 hqN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))

def A : HeckeAlg →+* Matrix (Fin m) (Fin m) ℂ :=
  (LinearMap.toMatrixAlgEquiv β).toRingEquiv.toRingHom.comp (cuspHeckeRep N)

theorem A_apply (t : HeckeAlg) : A N β t = LinearMap.toMatrix β β (cuspHeckeRep N t) := rfl

abbrev RatMat : Subring (Matrix (Fin m) (Fin m) ℂ) := ((Rat.castHom ℂ).mapMatrix).range

theorem mem_RatMat_iff (B : Matrix (Fin m) (Fin m) ℂ) :
    B ∈ RatMat (m := m) ↔ ∀ i j, B i j ∈ Set.range ((↑) : ℚ → ℂ) := by
  constructor
  · rintro ⟨B', rfl⟩ i j
    exact ⟨B' i j, rfl⟩
  · intro h
    choose g hg using h
    refine ⟨Matrix.of g, ?_⟩
    ext i j
    simp [hg]

include hT hU in
theorem A_heckeGen_mem (ℓ : Nat.Primes) : A N β (heckeGen ℓ) ∈ RatMat (m := m) := by
  rw [mem_RatMat_iff]
  intro i j
  rw [A_apply, cuspHeckeRep_heckeGen, LinearMap.toMatrix_apply]
  by_cases h : (ℓ : ℕ) ∣ N
  · rw [cuspHeckeGen_of_dvd N ℓ h]
    exact hU ℓ ℓ.prop h j i
  · rw [cuspHeckeGen_of_not_dvd N ℓ h]
    exact hT ℓ ℓ.prop h j i

include hT hU in
theorem A_mem (t : HeckeAlg) : A N β t ∈ RatMat (m := m) := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, show algebraMap ℤ HeckeAlg a = (a : HeckeAlg) from
      (eq_intCast _ a), map_intCast]
    exact intCast_mem _ a
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | mul_X p ℓ hp =>
    rw [map_mul]
    exact Subring.mul_mem _ hp (A_heckeGen_mem N β hT hU ℓ)

def ReMat : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) where
  carrier := {B | ∀ i j, (B i j).im = 0}
  add_mem' ha hb i j := by simp [ha i j, hb i j]
  zero_mem' i j := by simp
  smul_mem' r B hB i j := by simp [hB i j]

def ImMat : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) where
  carrier := {B | ∀ i j, (B i j).re = 0}
  add_mem' ha hb i j := by simp [ha i j, hb i j]
  zero_mem' i j := by simp
  smul_mem' r B hB i j := by simp [hB i j]

theorem ReMat_inf_ImMat : ReMat (m := m) ⊓ ImMat = ⊥ := by
  rw [eq_bot_iff]
  rintro B ⟨hre, him⟩
  rw [Submodule.mem_bot]
  ext i j
  apply Complex.ext
  · simpa using him i j
  · simpa using hre i j

theorem RatMat_le_ReMat (B : Matrix (Fin m) (Fin m) ℂ) (hB : B ∈ RatMat (m := m)) : B ∈ ReMat (m := m) := by
  rw [mem_RatMat_iff] at hB
  intro i j
  obtain ⟨q, hq⟩ := hB i j
  rw [← hq]
  exact Complex.ratCast_im q

theorem map_mulI_ReMat_le : (ReMat (m := m)).map mulI ≤ ImMat := by
  rintro _ ⟨B, hB, rfl⟩ i j
  simp [Matrix.smul_apply, hB i j]

abbrev RV' : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) := Submodule.span ℝ (Set.range (A N β))

abbrev CV' : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ) := Submodule.span ℂ (Set.range (A N β))

include hT hU in
theorem RV'_le_ReMat : RV' N β ≤ ReMat := by
  rw [Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact RatMat_le_ReMat _ (A_mem N β hT hU t)

include hT hU in
theorem RV'_inf_eq_bot : RV' N β ⊓ (RV' N β).map mulI = ⊥ := by
  rw [eq_bot_iff, ← ReMat_inf_ImMat]
  exact inf_le_inf (RV'_le_ReMat N β hT hU)
    ((Submodule.map_mono (RV'_le_ReMat N β hT hU)).trans map_mulI_ReMat_le)

def restrictEquiv : ((CV' N β).restrictScalars ℝ) ≃ₗ[ℝ] (CV' N β) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

include hT hU in

theorem finrank_RV' : finrank ℝ (RV' N β) = finrank ℂ (CV' N β) := by
  have hsup := restrictScalars_span_complex (E := Matrix (Fin m) (Fin m) ℂ) (Set.range (A N β))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (RV' N β) ((RV' N β).map mulI)
  rw [RV'_inf_eq_bot N β hT hU, finrank_bot, add_zero, ← hsup] at hdim
  have hmap : finrank ℝ ((RV' N β).map mulI) = finrank ℝ (RV' N β) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ mulI_injective (RV' N β))).symm
  have h2 : finrank ℝ ((CV' N β).restrictScalars ℝ) = 2 * finrank ℂ (CV' N β) := by
    rw [LinearEquiv.finrank_eq (restrictEquiv N β)]
    exact finrank_real_of_complex _
  have h3 : 2 * finrank ℂ (CV' N β) = finrank ℝ (RV' N β) + finrank ℝ (RV' N β) := by
    rw [← h2, hdim, hmap]
  omega

theorem finrank_CV' : finrank ℂ (CV' N β) = finrank ℂ (C N) := by
  have : CV' N β = (C N).map ((LinearMap.toMatrix β β : Module.End ℂ (V N) ≃ₗ[ℂ] _) :
      Module.End ℂ (V N) →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) := by
    rw [C_eq_span_range, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (LinearMap.toMatrix β β).injective (C N))).symm

theorem finrank_RV'_eq_RVℝ : finrank ℝ (RV' N β) = finrank ℝ (RVℝ N) := by
  let Ψ₂ : Module.End ℂ (V N) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    ((LinearMap.toMatrix β β : Module.End ℂ (V N) ≃ₗ[ℂ] _) :
      Module.End ℂ (V N) →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ).restrictScalars ℝ
  have : RV' N β = (RVℝ N).map Ψ₂ := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Ψ₂
    (by exact (LinearMap.toMatrix β β).injective) (RVℝ N))).symm

end Rational
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

theorem two_mul_g_eq {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (hst : PeriodLatticeHeckeStable N)
    {m : ℕ} (β : Module.Basis (Fin m) ℂ (V N))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin m),
      β.repr (CuspForm.heckeTLin 2 hℓ hℓN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin m),
      β.repr (CuspForm.heckeULin 2 hqN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
    (hB3c : finrank ℂ (C N) = finrank ℂ (V N)) :
    2 * finrank ℝ (Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ))) = n := by
  haveI : FiniteDimensional ℂ (V N) := Module.Finite.of_basis β
  rw [finrank_span_MK_real_eq N b hli hsp hst, ← finrank_RV'_eq_RVℝ N β, finrank_RV' N β hT hU,
    finrank_CV', hB3c, ← Subspace.dual_finrank_eq (K := ℂ) (V := V N), ← finrank_real_of_complex,
    finrank_eq_card_basis (bℝ N b hli hsp), Fintype.card_fin]

end W1A
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

namespace W1D

p2m_open "Module Matrix.Module Matrix"

variable {R₀ : Type} [CommRing R₀] {n : ℕ} (Mℤ : R₀ →+* Matrix (Fin n) (Fin n) ℤ)

def MK (K : Type) [CommRing K] : R₀ →+* Matrix (Fin n) (Fin n) K :=
  ((Int.castRingHom K).mapMatrix).comp Mℤ

theorem MK_apply (K : Type) [CommRing K] (t : R₀) : MK Mℤ K t = (Mℤ t).map (Int.cast : ℤ → K) := rfl

theorem MK_map (K : Type) [Field K] [CharZero K] (t : R₀) :
    (MK Mℤ ℚ t).map (algebraMap ℚ K) = MK Mℤ K t := by
  rw [MK_apply, MK_apply, Matrix.map_map]
  congr 1
  funext z
  simp

def Tℚ : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ) := Submodule.span ℚ (Set.range (MK Mℤ ℚ))

def g : ℕ := finrank ℚ (Tℚ Mℤ)

def c : Basis (Fin (g Mℤ)) ℚ (Tℚ Mℤ) := Module.finBasis ℚ (Tℚ Mℤ)

def cK (K : Type) [Field K] [CharZero K] (k : Fin (g Mℤ)) : Matrix (Fin n) (Fin n) K :=
  ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K)

theorem smul_map_algebraMap (K : Type) [Field K] [CharZero K] (q : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (q • A).map (algebraMap ℚ K) = (q : K) • A.map (algebraMap ℚ K) := by
  ext i j; simp

theorem eq_sum_of_mem_Tℚ (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ) = ∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ) := by
  have h := congrArg (Submodule.subtype (Tℚ Mℤ)) ((c Mℤ).sum_repr x).symm
  rw [map_sum] at h
  simpa using h

theorem map_mem_span_cK (K : Type) [Field K] [CharZero K] (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K) ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  rw [eq_sum_of_mem_Tℚ Mℤ x]
  rw [show (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ K)
      = (algebraMap ℚ K).mapMatrix (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ))
      from rfl, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [RingHom.mapMatrix_apply, smul_map_algebraMap]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem MK_mem_span_cK (K : Type) [Field K] [CharZero K] (t : R₀) :
    MK Mℤ K t ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  have hmem : MK Mℤ ℚ t ∈ Tℚ Mℤ := Submodule.subset_span (Set.mem_range_self t)
  rw [← MK_map Mℤ K t]
  exact map_mem_span_cK Mℤ K ⟨MK Mℤ ℚ t, hmem⟩

theorem map_mem_of_mem_Tℚ (K : Type) [Field K] [CharZero K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ t, MK Mℤ K t ∈ S) {x : Matrix (Fin n) (Fin n) ℚ} (hx : x ∈ Tℚ Mℤ) :
    x.map (algebraMap ℚ K) ∈ S := by
  refine Submodule.span_induction (p := fun x _ => x.map (algebraMap ℚ K) ∈ S) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨t, rfl⟩
    rw [MK_map]; exact hS t
  · simp only [Matrix.map_zero, map_zero]; exact S.zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.map_add _ (map_add (algebraMap ℚ K))]; exact S.add_mem hx hy
  · intro r x _ hx
    rw [smul_map_algebraMap]; exact S.smul_mem _ hx

section Square

variable (hn : 2 * g Mℤ = n)

def σ : Fin 2 × Fin (g Mℤ) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp [hn])

def Φ (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (cK Mℤ K ((σ Mℤ hn).symm j).2 *ᵥ v ((σ Mℤ hn).symm j).1) i

theorem Φ_col (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) (ak : Fin 2 × Fin (g Mℤ)) :
    (Φ Mℤ hn K v).col (σ Mℤ hn ak) = cK Mℤ K ak.2 *ᵥ v ak.1 := by
  funext i
  simp [Φ]

theorem Φ_map (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → ℚ) :
    (Φ Mℤ hn ℚ v).map (algebraMap ℚ K) = Φ Mℤ hn K (fun a => (algebraMap ℚ K) ∘ v a) := by
  ext i j
  simp only [Φ, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  simp only [cK, Matrix.map_map]
  congr 2

theorem span_cols_Φ_eq_top (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    Submodule.span K (Set.range (Φ Mℤ hn K w).col) = ⊤ := by
  apply top_le_iff.mp
  rw [← hw]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨t, a⟩, rfl⟩
  have hmem := MK_mem_span_cK Mℤ K t
  simp only [SetLike.mem_coe]

  refine Submodule.span_induction (p := fun x _ => x *ᵥ w a ∈ Submodule.span K (Set.range (Φ Mℤ hn K w).col))
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨σ Mℤ hn (a, k), ?_⟩
    exact Φ_col Mℤ hn K w (a, k)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ r hx

theorem isUnit_Φ (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    IsUnit (Φ Mℤ hn K w) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_cols_Φ_eq_top Mℤ hn K w hw).ge (by simp)

theorem span_cols_Φ_of_isUnit (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K)
    (hv : IsUnit (Φ Mℤ hn K v)) :
    Submodule.span K (Set.range (Φ Mℤ hn K v).col) = ⊤ := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit] at hv
  exact hv.span_eq_top_of_card_eq_finrank' (by simp)

theorem continuous_det_Φ : Continuous fun v : Fin 2 → Fin n → ℝ => (Φ Mℤ hn ℝ v).det := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Φ, Matrix.of_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem exists_rat_isUnit_Φ
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : R₀ × Fin 2 => MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ v : Fin 2 → Fin n → ℚ, IsUnit (Φ Mℤ hn ℚ v) := by
  obtain ⟨w, hw⟩ := hw
  have hU : IsOpen {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0} :=
    isOpen_ne_fun (continuous_det_Φ Mℤ hn) continuous_const
  have hne : {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0}.Nonempty :=
    ⟨w, by
      have := isUnit_Φ Mℤ hn ℝ w hw
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
      exact this⟩
  have hdense : DenseRange (fun v : Fin 2 → Fin n → ℚ => fun a => fun j => ((v a j : ℚ) : ℝ)) := by
    have h1 : DenseRange (fun x : Fin n → ℚ => fun j => ((x j : ℚ) : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact DenseRange.piMap fun _ => h1
  obtain ⟨v, hv⟩ := hdense.exists_mem_open hU hne
  refine ⟨v, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply hv
  have hmap := RingHom.map_det (algebraMap ℚ ℝ) (Φ Mℤ hn ℚ v)
  rw [h0, map_zero, RingHom.mapMatrix_apply, Φ_map] at hmap
  exact hmap.symm

end Square
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

end W1D
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A"

namespace W1D

p2m_open "Module Matrix.Module"

variable {n : ℕ}

def flat (K : Type) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flat_injective (K : Type) [CommRing K] : Function.Injective (flat (n := n) K) := by
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem ker_flat (K : Type) [CommRing K] : LinearMap.ker (flat (n := n) K) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (flat_injective K)

def castMat : Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
  ((Algebra.ofId ℚ ℝ).mapMatrix).toLinearMap

@[scoped simp] theorem castMat_apply (A : Matrix (Fin n) (Fin n) ℚ) :
    castMat A = A.map (algebraMap ℚ ℝ) := rfl

theorem linearIndependent_real_of_rat {ι : Type*} (v : ι → Matrix (Fin n) (Fin n) ℚ)
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℝ (fun i => (v i).map (algebraMap ℚ ℝ)) := by

  have h1 : LinearIndependent ℚ (fun i => flat ℚ (v i)) := hv.map' (flat ℚ) (ker_flat ℚ)
  have h2 : LinearIndependent ℝ (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mpr h1
  have h3 : (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) = fun i => flat ℝ ((v i).map (algebraMap ℚ ℝ)) := by
    funext i; funext ij; rfl
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat ℝ) h2

theorem finrank_real_span_eq {ι : Type*} (f : ι → Matrix (Fin n) (Fin n) ℚ) :
    finrank ℝ (Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ))) =
      finrank ℚ (Submodule.span ℚ (Set.range f)) := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range f)
  have hfin : s.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  haveI : Fintype s := hfin.fintype

  have hq : finrank ℚ (Submodule.span ℚ (Set.range f)) = Fintype.card s := by
    rw [← hspan, ← finrank_span_eq_card (b := ((↑) : s → Matrix (Fin n) (Fin n) ℚ)) hli]
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have hli' : LinearIndependent ℝ (fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ)) :=
    linearIndependent_real_of_rat _ hli
  have hspan' : Submodule.span ℝ (Set.range fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))
      = Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ)) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hs hx
      exact ⟨i, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : f i ∈ Submodule.span ℚ s := by rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

      have : castMat (f i) ∈ (Submodule.span ℚ s).map castMat := Submodule.mem_map_of_mem hi
      rw [Submodule.map_span] at this
      have hle : Submodule.span ℚ (castMat '' s) ≤
          (Submodule.span ℝ (Set.range fun i : s =>
            ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))).restrictScalars ℚ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact hle this
  rw [← hspan', finrank_span_eq_card hli', hq]

end W1D
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D"

namespace W1D

p2m_open "Module Matrix.Module Matrix"

variable {R₀ : Type} [CommRing R₀] {n : ℕ} (Mℤ : R₀ →+* Matrix (Fin n) (Fin n) ℤ)

section RatDescent

def Tq : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ) :=
  Algebra.adjoin ℚ (Set.range (MK Mℤ ℚ))

scoped instance : IsMulCommutative (Tq Mℤ) :=
  Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingTq : CommRing (Tq Mℤ) := inferInstance

def φ : R₀ →+* Tq Mℤ :=
  (MK Mℤ ℚ).codRestrict (Tq Mℤ).toSubring
    fun t => Algebra.subset_adjoin (Set.mem_range_self t)

@[scoped simp] theorem coe_φ (t : R₀) : (φ Mℤ t : Matrix (Fin n) (Fin n) ℚ) = MK Mℤ ℚ t := rfl

theorem adjoin_range_φ : Algebra.adjoin ℚ (Set.range (φ Mℤ)) = ⊤ := by
  apply Subalgebra.map_injective (f := (Tq Mℤ).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
  rfl

theorem toSubmodule_Tq_le : Subalgebra.toSubmodule (Tq Mℤ) ≤
    Submodule.span ℚ (Set.range (cK Mℤ ℚ)) := by
  rw [Tq, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure (Set.range (MK Mℤ ℚ)) : Set (Matrix (Fin n) (Fin n) ℚ)) =
      Set.range (MK Mℤ ℚ) := by
    refine le_antisymm ?_ Submonoid.subset_closure
    have : Set.range (MK Mℤ ℚ) = (MonoidHom.mrange (MK Mℤ ℚ : R₀ →* Matrix (Fin n) (Fin n) ℚ) :
        Set (Matrix (Fin n) (Fin n) ℚ)) := (MonoidHom.coe_mrange _).symm
    rw [this]
    exact Submonoid.closure_le.mpr (le_of_eq this)
  rw [hcl]
  exact Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact MK_mem_span_cK Mℤ ℚ t)

theorem finrank_Tq_le : finrank ℚ (Tq Mℤ) ≤ g Mℤ := by
  calc finrank ℚ (Tq Mℤ)
      = finrank ℚ (Subalgebra.toSubmodule (Tq Mℤ)) := (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank ℚ (Submodule.span ℚ (Set.range (cK Mℤ ℚ))) :=
        Submodule.finrank_mono (toSubmodule_Tq_le Mℤ)
    _ ≤ Fintype.card (Fin (g Mℤ)) := finrank_range_le_card _
    _ = g Mℤ := Fintype.card_fin _

theorem cK_mem_Tq (k : Fin (g Mℤ)) : cK Mℤ ℚ k ∈ Tq Mℤ := by

  have h := map_mem_of_mem_Tℚ Mℤ ℚ (Subalgebra.toSubmodule (Tq Mℤ))
    (fun t => Algebra.subset_adjoin (Set.mem_range_self t)) (c Mℤ k).2
  exact h

variable (hn : 2 * g Mℤ = n) (vq : Fin 2 → Fin n → ℚ)

def vp : Fin 2 → Fin n → ℚ := vq

def ψ : (Fin 2 → Tq Mℤ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun s := ∑ a, ((s a : Tq Mℤ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ vp vq a
  map_add' s s' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem ψ_apply (s : Fin 2 → Tq Mℤ) :
    ψ Mℤ vq s = ∑ a, ((s a : Tq Mℤ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ vp vq a := rfl

theorem ψ_equivariant (t : R₀) (s : Fin 2 → Tq Mℤ) :
    ψ Mℤ vq (φ Mℤ t • s) = MK Mℤ ℚ t *ᵥ ψ Mℤ vq s := by
  simp only [ψ_apply, Pi.smul_apply, smul_eq_mul, Subalgebra.coe_mul, coe_φ, Matrix.mulVec_sum,
    Matrix.mulVec_mulVec]

theorem ψ_surjective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Surjective (ψ Mℤ vq) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hvp : IsUnit (Φ Mℤ hn ℚ (vp vq)) := hv
  rw [← span_cols_Φ_of_isUnit Mℤ hn ℚ (vp vq) hvp, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨⟨a, k⟩, rfl⟩ := (σ Mℤ hn).surjective j
  rw [Φ_col]
  refine ⟨Pi.single a ⟨cK Mℤ ℚ k, cK_mem_Tq Mℤ k⟩, ?_⟩
  rw [ψ_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem finrank_source_le : finrank ℚ (Fin 2 → Tq Mℤ) ≤ 2 * g Mℤ := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_le_mul_left 2 (finrank_Tq_le Mℤ)

theorem ψ_bijective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Bijective (ψ Mℤ vq) := by
  have hsurj := ψ_surjective Mℤ hn vq hv
  refine ⟨?_, hsurj⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (ψ Mℤ vq)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  have hle := finrank_source_le Mℤ
  rw [hn] at hle
  have hker : finrank ℚ (LinearMap.ker (ψ Mℤ vq)) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

theorem exists_equiv (hv : IsUnit (Φ Mℤ hn ℚ vq)) :
    ∃ e : (Fin n → ℚ) ≃ₗ[ℚ] (Fin 2 → Tq Mℤ),
      ∀ (t : R₀) (v : Fin n → ℚ), e (MK Mℤ ℚ t *ᵥ v) = φ Mℤ t • e v := by
  let e := (LinearEquiv.ofBijective (ψ Mℤ vq) (ψ_bijective Mℤ hn vq hv)).symm
  refine ⟨e, fun t v => ?_⟩
  apply e.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change MK Mℤ ℚ t *ᵥ v = ψ Mℤ vq (φ Mℤ t • e v)
  rw [ψ_equivariant]
  congr 1
  exact (LinearEquiv.ofBijective (ψ Mℤ vq) (ψ_bijective Mℤ hn vq hv)).apply_symm_apply v |>.symm

theorem toSubmodule_Tq_eq_span : Subalgebra.toSubmodule (Tq Mℤ) =
    Submodule.span ℚ (Set.range (MK Mℤ ℚ)) := by
  rw [Tq, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure (Set.range (MK Mℤ ℚ)) : Set (Matrix (Fin n) (Fin n) ℚ)) =
      Set.range (MK Mℤ ℚ) := by
    refine le_antisymm ?_ Submonoid.subset_closure
    have : Set.range (MK Mℤ ℚ) = (MonoidHom.mrange (MK Mℤ ℚ : R₀ →* Matrix (Fin n) (Fin n) ℚ) :
        Set (Matrix (Fin n) (Fin n) ℚ)) := (MonoidHom.coe_mrange _).symm
    rw [this]
    exact Submonoid.closure_le.mpr (le_of_eq this)
  rw [hcl]

theorem exists_nsmul_eq_MK {x : Matrix (Fin n) (Fin n) ℚ}
    (hx : x ∈ Submodule.span ℚ (Set.range (MK Mℤ ℚ))) :
    ∃ (e : ℕ) (t : R₀), e ≠ 0 ∧ (e : ℚ) • x = MK Mℤ ℚ t := by
  refine Submodule.span_induction (p := fun x _ => ∃ (e : ℕ) (t : R₀), e ≠ 0 ∧ (e : ℚ) • x = MK Mℤ ℚ t)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨t, rfl⟩
    exact ⟨1, t, one_ne_zero, by simp⟩
  · exact ⟨1, 0, one_ne_zero, by simp⟩
  · rintro x y - - ⟨e, t, he, hxe⟩ ⟨e', t', he', hye⟩
    refine ⟨e * e', (e' : R₀) * t + (e : R₀) * t', mul_ne_zero he he', ?_⟩
    rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← nsmul_eq_mul, ← nsmul_eq_mul,
      ← hxe, ← hye, ← Nat.cast_smul_eq_nsmul ℚ e', ← Nat.cast_smul_eq_nsmul ℚ e, smul_smul,
      smul_smul, Nat.cast_mul, smul_add, mul_comm (e' : ℚ) (e : ℚ)]
  · rintro r x - ⟨e, t, he, hxe⟩
    refine ⟨e * r.den, (r.num : R₀) * t, mul_ne_zero he r.den_ne_zero, ?_⟩
    rw [map_mul, map_intCast, ← zsmul_eq_mul, ← hxe, ← Int.cast_smul_eq_zsmul ℚ r.num, smul_smul,
      smul_smul, Nat.cast_mul]
    congr 1
    rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]

end RatDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D"

end W1D
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D"

namespace P2MBettiZ

p2m_open "Module Matrix.Module"

variable {R₀ : Type} [CommRing R₀] {Λ : Type} [AddCommGroup Λ] (ρ : R₀ →+* Module.End ℤ Λ)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)

def M : R₀ →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp ρ

theorem M_apply (t : R₀) : M ρ b t = LinearMap.toMatrix b b (ρ t) := rfl

def castc (x : Λ) : Fin n → ℚ := fun j => ((b.repr x j : ℤ) : ℚ)

theorem castc_apply (x : Λ) (j : Fin n) : castc b x j = ((b.repr x j : ℤ) : ℚ) := rfl

theorem castc_injective : Function.Injective (castc b) := by
  intro x y hxy
  apply b.repr.injective
  ext j
  exact Int.cast_injective (congrFun hxy j)

theorem castc_add (x y : Λ) : castc b (x + y) = castc b x + castc b y := by
  funext j; simp [castc]

theorem castc_zero : castc b (0 : Λ) = 0 := by
  funext j; simp [castc]

theorem castc_nsmul (k : ℕ) (x : Λ) : castc b (k • x) = (k : ℚ) • castc b x := by
  funext j; simp [castc]

theorem castc_zsmul (k : ℤ) (x : Λ) : castc b (k • x) = (k : ℚ) • castc b x := by
  funext j; simp [castc]

theorem castc_ρ (t : R₀) (x : Λ) : castc b (ρ t x) = W1D.MK (M ρ b) ℚ t *ᵥ castc b x := by
  funext i
  have h := LinearMap.toMatrix_mulVec_repr b b (ρ t) x
  rw [← M_apply] at h
  have hi := congrArg (fun f : Fin n → ℤ => ((f i : ℤ) : ℚ)) h
  rw [W1D.MK_apply, castc_apply, ← hi,
    show ((((M ρ b t) *ᵥ ⇑(b.repr x)) i : ℤ) : ℚ) = (Int.castRingHom ℚ) (((M ρ b t) *ᵥ ⇑(b.repr x)) i)
      from rfl, RingHom.map_mulVec]
  rfl

theorem castc_equivFun_symm (z : Fin n → ℤ) : castc b (b.equivFun.symm z) = fun j => ((z j : ℤ) : ℚ) := by
  funext j
  rw [castc_apply]
  have := b.equivFun.apply_symm_apply z
  rw [Module.Basis.equivFun_apply] at this
  rw [this]

theorem exists_of_isUnit (hn : 2 * W1D.g (M ρ b) = n) (vz : Fin 2 → Fin n → ℤ)
    (hunit : IsUnit (W1D.Φ (M ρ b) hn ℚ fun a j => ((vz a j : ℤ) : ℚ))) :
    ∃ (v w : Λ) (d : ℕ), d ≠ 0 ∧
      (∀ x : Λ, ∃ s t : R₀, d • x = ρ s v + ρ t w) ∧
      (∀ s t : R₀, ρ s v + ρ t w = 0 → ρ s = 0 ∧ ρ t = 0) := by
  classical
  set Mℤ := M ρ b with hMℤ
  let w : Fin 2 → Fin n → ℚ := fun a j => ((vz a j : ℤ) : ℚ)
  let vΛ : Fin 2 → Λ := fun a => b.equivFun.symm (vz a)
  have castc_vΛ : ∀ a, castc b (vΛ a) = w a := fun a => castc_equivFun_symm b (vz a)

  have hbij := W1D.ψ_bijective Mℤ hn w hunit
  have hψ : ∀ s : Fin 2 → W1D.Tq Mℤ,
      W1D.ψ Mℤ w s = ((s 0 : W1D.Tq Mℤ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ w 0 +
        ((s 1 : W1D.Tq Mℤ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ w 1 := fun s => by
    rw [W1D.ψ_apply, Fin.sum_univ_two]
    rfl

  let Λ' : AddSubgroup Λ :=
    { carrier := {x | ∃ s t : R₀, x = ρ s (vΛ 0) + ρ t (vΛ 1)}
      zero_mem' := ⟨0, 0, by simp⟩
      add_mem' := by
        rintro x y ⟨s, t, rfl⟩ ⟨s', t', rfl⟩
        exact ⟨s + s', t + t', by simp only [map_add, LinearMap.add_apply]; abel⟩
      neg_mem' := by
        rintro x ⟨s, t, rfl⟩
        exact ⟨-s, -t, by simp only [map_neg, LinearMap.neg_apply, neg_add]⟩ }
  have hΛ'_nsmul : ∀ (k : ℕ) {x}, x ∈ Λ' → k • x ∈ Λ' := fun k x hx => AddSubgroup.nsmul_mem _ hx k
  have hΛ'_zsmul : ∀ (k : ℤ) {x}, x ∈ Λ' → k • x ∈ Λ' := fun k x hx => AddSubgroup.zsmul_mem _ hx k

  have hbasis : ∀ i, ∃ dᵢ : ℕ, dᵢ ≠ 0 ∧ dᵢ • b i ∈ Λ' := by
    intro i
    obtain ⟨sq, hsq⟩ := hbij.2 (castc b (b i))
    have hmem : ∀ a, ((sq a : W1D.Tq Mℤ) : Matrix (Fin n) (Fin n) ℚ) ∈
        Submodule.span ℚ (Set.range (W1D.MK Mℤ ℚ)) := fun a => by
      rw [← W1D.toSubmodule_Tq_eq_span]
      exact (sq a).2
    obtain ⟨e₀, t₀, he₀, h₀⟩ := W1D.exists_nsmul_eq_MK Mℤ (hmem 0)
    obtain ⟨e₁, t₁, he₁, h₁⟩ := W1D.exists_nsmul_eq_MK Mℤ (hmem 1)
    refine ⟨e₀ * e₁, mul_ne_zero he₀ he₁, (e₁ : R₀) * t₀, (e₀ : R₀) * t₁, ?_⟩
    apply castc_injective b
    rw [castc_nsmul, castc_add, castc_ρ, castc_ρ, castc_vΛ, castc_vΛ, ← hsq, hψ,
      map_mul, map_mul, map_natCast, map_natCast, ← nsmul_eq_mul, ← nsmul_eq_mul, ← h₀, ← h₁,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      ← Nat.cast_smul_eq_nsmul ℚ e₁, ← Nat.cast_smul_eq_nsmul ℚ e₀, smul_smul, smul_smul,
      Nat.cast_mul, smul_add, mul_comm (e₁ : ℚ) (e₀ : ℚ)]
  choose dᵢ hdᵢ hdᵢmem using hbasis
  refine ⟨vΛ 0, vΛ 1, ∏ i, dᵢ i, Finset.prod_ne_zero_iff.mpr fun i _ => hdᵢ i, ?_, ?_⟩
  ·
    intro x
    have hbi : ∀ i, (∏ j, dᵢ j) • b i ∈ Λ' := by
      intro i
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem dᵢ (Finset.mem_univ i)
      rw [hk, mul_comm, mul_smul]
      exact hΛ'_nsmul k (hdᵢmem i)
    have hx : (∏ j, dᵢ j) • x ∈ Λ' := by
      rw [show (∏ j, dᵢ j) • x = (∏ j, dᵢ j) • ∑ i, b.repr x i • b i by rw [b.sum_repr x],
        Finset.smul_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [smul_comm]
      exact hΛ'_zsmul _ (hbi i)
    obtain ⟨s, t, hst'⟩ := hx
    exact ⟨s, t, hst'⟩
  ·
    intro s t hst0
    have hcast := congrArg (castc b) hst0
    rw [castc_add, castc_ρ, castc_ρ, castc_vΛ, castc_vΛ, castc_zero] at hcast
    have hmems : W1D.MK Mℤ ℚ s ∈ W1D.Tq Mℤ := Algebra.subset_adjoin (Set.mem_range_self s)
    have hmemt : W1D.MK Mℤ ℚ t ∈ W1D.Tq Mℤ := Algebra.subset_adjoin (Set.mem_range_self t)
    let sq : Fin 2 → W1D.Tq Mℤ := ![⟨W1D.MK Mℤ ℚ s, hmems⟩, ⟨W1D.MK Mℤ ℚ t, hmemt⟩]
    have hψsq : W1D.ψ Mℤ w sq = 0 := by
      rw [hψ]
      exact hcast
    have hsq0 : sq = 0 := hbij.1 (by rw [hψsq, map_zero])
    have hs : W1D.MK Mℤ ℚ s = 0 := by
      have h0 := congrFun hsq0 0
      have := congrArg (Subtype.val) h0
      simpa [sq] using this
    have ht : W1D.MK Mℤ ℚ t = 0 := by
      have h1 := congrFun hsq0 1
      have := congrArg (Subtype.val) h1
      simpa [sq] using this
    have hMK0 : ∀ u : R₀, W1D.MK Mℤ ℚ u = 0 → ρ u = 0 := by
      intro u hu
      rw [W1D.MK_apply] at hu
      have hM : Mℤ u = 0 := by
        refine Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_
        show (Mℤ u).map (Int.cast : ℤ → ℚ) = (0 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℚ)
        rw [hu, Matrix.map_zero (Int.cast : ℤ → ℚ) Int.cast_zero]
      rw [hMℤ, M_apply] at hM
      exact (LinearMap.toMatrix b b).map_eq_zero_iff.mp hM
    exact ⟨hMK0 s hs, hMK0 t ht⟩

end P2MBettiZ
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D"

namespace P2MBettiFinal

p2m_open "Module Matrix.Module ModularCurve"

theorem exists_int_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℚ) :
    ∃ (D : ℕ) (z : ι → ℤ), D ≠ 0 ∧ ∀ i, (z i : ℚ) = (D : ℚ) * v i := by
  refine ⟨∏ i, (v i).den, fun i => (∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ)) * (v i).num,
    Finset.prod_ne_zero_iff.mpr fun i _ => (v i).den_ne_zero, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ (fun j => (v j).den) (Finset.mem_univ i)]
  push_cast
  rw [mul_assoc, Rat.den_mul_eq_num]

variable (N : ℕ) [NeZero N]

theorem main : ∃ (v w : periodLattice N) (d : ℕ), d ≠ 0 ∧
      (∀ x : periodLattice N, ∃ s t : HeckeAlg,
        d • x = periodLatticeHeckeEnd N s v + periodLatticeHeckeEnd N t w) ∧
      (∀ s t : HeckeAlg, periodLatticeHeckeEnd N s v + periodLatticeHeckeEnd N t w = 0 →
        periodLatticeHeckeEnd N s = 0 ∧ periodLatticeHeckeEnd N t = 0) := by
  classical

  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  obtain ⟨n, b, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  obtain ⟨m, β, hT, hU⟩ := CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast N
  have hB3a : ∀ T : Module.End ℂ (W1A.V N), T ∈ W1A.C N →
      (∀ f : W1A.V N, ModularFormClass.qCoeff (⇑(T f)) 1 = 0) → T = 0 :=
    fun T hT h => CuspForm.eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero N T hT h
  have hB3c : finrank ℂ (W1A.C N) = finrank ℂ (W1A.V N) :=
    CuspForm.finrank_span_heckeAlgebra_eq_finrank N
  haveI : FiniteDimensional ℂ (W1A.V N) := Module.Finite.of_basis β

  let Mℤ : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ := P2MBettiZ.M (periodLatticeHeckeEnd N) b
  have hMW : W1A.Mℤ N b = Mℤ := rfl

  have hn : 2 * W1D.g Mℤ = n := by
    have h := W1A.two_mul_g_eq N b hli hsp hst β hT hU hB3c
    have hr : (fun t : HeckeAlg => (W1A.Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
        fun t : HeckeAlg => (W1D.MK Mℤ ℚ t).map (algebraMap ℚ ℝ) := by
      funext t
      rw [W1D.MK_map]
      rfl
    rw [hr, W1D.finrank_real_span_eq] at h
    exact h

  have hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => W1D.MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤ := by
    rw [← hMW]
    exact W1A.exists_w N b hli hsp hst (W1A.span_real_eq_top N hB3a hB3c)

  obtain ⟨vq, hvq⟩ := W1D.exists_rat_isUnit_Φ Mℤ hn hw

  obtain ⟨D, vz, hD, hvz⟩ := exists_int_eq_mul (fun aj : Fin 2 × Fin n => vq aj.1 aj.2)
  have hunit : IsUnit (W1D.Φ Mℤ hn ℚ fun a j => ((vz (a, j) : ℤ) : ℚ)) := by
    have hΦ : (W1D.Φ Mℤ hn ℚ fun a j => ((vz (a, j) : ℤ) : ℚ)) = (D : ℚ) • W1D.Φ Mℤ hn ℚ vq := by
      ext i j
      have hfun : (fun a j' => ((vz (a, j') : ℤ) : ℚ)) = fun a => (D : ℚ) • vq a := by
        funext a j'; rw [hvz (a, j')]; rfl
      rw [hfun]
      simp only [W1D.Φ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec_smul,
        Pi.smul_apply]
    rw [hΦ, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hD)).pow _).mul
      ((Matrix.isUnit_iff_isUnit_det _).mp hvq)
  exact P2MBettiZ.exists_of_isUnit (periodLatticeHeckeEnd N) b hn (fun a j => vz (a, j)) hunit

end P2MBettiFinal
p2m_reactivate "P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1C P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1A P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice.W1D"

theorem solution (N : ℕ) [NeZero N] :
    ∃ (v w : ModularCurve.periodLattice N) (d : ℕ), d ≠ 0 ∧
      (∀ x : ModularCurve.periodLattice N, ∃ s t : ModularCurve.HeckeAlg,
        d • x = ModularCurve.periodLatticeHeckeEnd N s v + ModularCurve.periodLatticeHeckeEnd N t w) ∧
      (∀ s t : ModularCurve.HeckeAlg,
        ModularCurve.periodLatticeHeckeEnd N s v + ModularCurve.periodLatticeHeckeEnd N t w = 0 →
        ModularCurve.periodLatticeHeckeEnd N s = 0 ∧ ModularCurve.periodLatticeHeckeEnd N t = 0) :=
  P2MBettiFinal.main N

end
end S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice
end P2MW
export P2MW.S_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice (solution)
