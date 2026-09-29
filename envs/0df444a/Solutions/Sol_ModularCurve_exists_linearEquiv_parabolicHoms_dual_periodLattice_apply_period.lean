-- Prove2me | solution 1 for ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5112dda2-1958-5413-b7da-532a91501fa2

import Mathlib
import Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_period
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
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
set_option linter.unusedSectionVars false

open scoped MatrixGroups

noncomputable section

namespace CpairK2

variable (N : ℕ) [NeZero N]

theorem exists_basis_periodLattice_card_eq :
    ∃ (m : ℕ) (_ : Module.Basis (Fin m) ℤ (ModularCurve.periodLattice N)),
      m = 2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  obtain ⟨m, c, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  refine ⟨m, c, ?_⟩
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2
  let bR : Module.Basis (Fin m) ℝ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
    Module.Basis.mk hli (by rw [hsp])
  have h1 : Module.finrank ℝ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = m := by
    rw [Module.finrank_eq_card_basis bR, Fintype.card_fin]
  have h2 : Module.finrank ℝ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) =
      2 * Module.finrank ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      Complex.finrank_real_complex]
  rw [← h1, h2, Subspace.dual_finrank_eq]

theorem exists_basis_parabolicHoms_card_le :
    ∃ (n : ℕ) (_ : Module.Basis (Fin n) ℤ
        (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)),
      n ≤ 2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  obtain ⟨n, b, hb⟩ :=
    ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (CongruenceSubgroup.Gamma0 N)
  obtain ⟨bR, -⟩ := hb ℝ
  refine ⟨n, b, ?_⟩
  have h1 : Module.finrank ℝ
      (ModularCurve.Period.parabolicHoms ℝ (CongruenceSubgroup.Gamma0 N) ℝ) = n := by
    rw [Module.finrank_eq_card_basis bR, Fintype.card_fin]
  rw [← h1]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm N

def rel : Submodule ℤ (CongruenceSubgroup.Gamma0 N →₀ ℤ) :=
  Submodule.span ℤ
    ({x | ∃ γ δ : CongruenceSubgroup.Gamma0 N,
        x = Finsupp.single (γ * δ) 1 - Finsupp.single γ 1 - Finsupp.single δ 1} ∪
     {x | ∃ γ : CongruenceSubgroup.Gamma0 N,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 ∧ x = Finsupp.single γ 1})

abbrev Q : Type := (CongruenceSubgroup.Gamma0 N →₀ ℤ) ⧸ rel N

def cls (γ : CongruenceSubgroup.Gamma0 N) : Q N := Submodule.Quotient.mk (Finsupp.single γ 1)

omit [NeZero N] in
theorem cls_mul (γ δ : CongruenceSubgroup.Gamma0 N) : cls N (γ * δ) = cls N γ + cls N δ := by
  rw [cls, cls, cls, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have : Finsupp.single (γ * δ) (1 : ℤ) - (Finsupp.single γ 1 + Finsupp.single δ 1) =
      Finsupp.single (γ * δ) 1 - Finsupp.single γ 1 - Finsupp.single δ 1 := by abel
  rw [this]
  exact Submodule.subset_span (Or.inl ⟨γ, δ, rfl⟩)

omit [NeZero N] in
theorem cls_eq_zero_of_trace (γ : CongruenceSubgroup.Gamma0 N)
    (h : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : cls N γ = 0 := by
  rw [cls, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Or.inr ⟨γ, h, rfl⟩)

omit [NeZero N] in

theorem rel_le_ker (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) :
    rel N ≤ LinearMap.ker (Finsupp.linearCombination ℤ
      (fun γ : CongruenceSubgroup.Gamma0 N =>
        (ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ) (Additive.ofMul γ))) := by
  apply Submodule.span_le.mpr
  rintro x (⟨γ, δ, rfl⟩ | ⟨γ, hγ, rfl⟩)
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul, ofMul_mul, map_add]
    abel
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single, one_smul]
    exact ψ.2 γ hγ

noncomputable def barOf (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) :
    Q N →ₗ[ℤ] ℤ :=
  (rel N).liftQ _ (rel_le_ker N ψ)

@[scoped simp] theorem barOf_cls (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (γ : CongruenceSubgroup.Gamma0 N) :
    barOf N ψ (cls N γ) = (ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ) (Additive.ofMul γ) := by
  show (rel N).liftQ _ (rel_le_ker N ψ) (Submodule.Quotient.mk (Finsupp.single γ 1)) = _
  rw [Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]

def ofBar (χ : Q N →ₗ[ℤ] ℤ) :
    ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ :=
  ⟨{ toFun := fun x => χ (cls N (Additive.toMul x))
     map_zero' := by
       have h := cls_mul N 1 1
       rw [mul_one] at h
       have h0 : cls N 1 = 0 := by
         have := congrArg (fun t => t - cls N 1) h
         simp at this
         exact this.symm
       show χ (cls N 1) = 0
       rw [h0, map_zero]
     map_add' := fun x y => by
       show χ (cls N (Additive.toMul x * Additive.toMul y)) = _
       rw [cls_mul, map_add] },
   fun γ hγ => by
     show χ (cls N γ) = 0
     rw [cls_eq_zero_of_trace N γ hγ, map_zero]⟩

@[scoped simp] theorem ofBar_apply (χ : Q N →ₗ[ℤ] ℤ) (γ : CongruenceSubgroup.Gamma0 N) :
    (ofBar N χ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ) (Additive.ofMul γ) = χ (cls N γ) := rfl

noncomputable def dualEquiv :
    ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ ≃ₗ[ℤ] Module.Dual ℤ (Q N) where
  toFun := barOf N
  invFun := ofBar N
  map_add' ψ ψ' := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : CongruenceSubgroup.Gamma0 N →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf N (ψ + ψ') (cls N γ) = n • (barOf N ψ (cls N γ) + barOf N ψ' (cls N γ))
    rw [barOf_cls, barOf_cls, barOf_cls]
    rfl
  map_smul' k ψ := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : CongruenceSubgroup.Gamma0 N →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf N (k • ψ) (cls N γ) = n • (k • barOf N ψ (cls N γ))
    rw [barOf_cls, barOf_cls]
    rfl
  left_inv ψ := by
    apply Subtype.ext
    ext x
    show barOf N ψ (cls N (Additive.toMul x)) = _
    rw [barOf_cls]
    rfl
  right_inv χ := by
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro γ n
    have hs : (Finsupp.single γ n : CongruenceSubgroup.Gamma0 N →₀ ℤ) = n • Finsupp.single γ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hs, map_smul]
    show n • barOf N (ofBar N χ) (cls N γ) = n • χ (cls N γ)
    rw [barOf_cls, ofBar_apply]

def perΛ (γ : CongruenceSubgroup.Gamma0 N) : ModularCurve.periodLattice N :=
  ⟨ModularCurve.period N γ, ModularCurve.period_mem_periodLattice N γ⟩

theorem span_perΛ : Submodule.span ℤ (Set.range (perΛ N)) = ⊤ := by
  apply Submodule.map_injective_of_injective (ModularCurve.periodLattice N).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

theorem rel_le_ker_period :
    rel N ≤ LinearMap.ker (Finsupp.linearCombination ℤ (perΛ N)) := by
  obtain ⟨Φ, hΦpar, hΦ⟩ := ModularCurve.exists_isParabolicHom_apply_eq_period N
  have hval : ∀ γ, ((perΛ N γ : ModularCurve.periodLattice N) :
      Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = Φ (Additive.ofMul γ) :=
    fun γ => (hΦ γ).symm
  apply Submodule.span_le.mpr
  rintro x (⟨γ, δ, rfl⟩ | ⟨γ, hγ, rfl⟩)
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul]
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, hval, ofMul_mul, map_add]
    abel
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single, one_smul]
    apply Subtype.ext
    rw [hval, ZeroMemClass.coe_zero]
    exact hΦpar γ hγ

def phiBar : Q N →ₗ[ℤ] ModularCurve.periodLattice N :=
  (rel N).liftQ _ (rel_le_ker_period N)

@[scoped simp] theorem phiBar_cls (γ : CongruenceSubgroup.Gamma0 N) : phiBar N (cls N γ) = perΛ N γ := by
  show (rel N).liftQ _ (rel_le_ker_period N) (Submodule.Quotient.mk (Finsupp.single γ 1)) = _
  rw [Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]

theorem phiBar_surjective : Function.Surjective (phiBar N) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_perΛ N, Submodule.span_le]
  rintro _ ⟨γ, rfl⟩
  exact ⟨cls N γ, phiBar_cls N γ⟩

theorem dual_ker_phiBar_eq_zero (χ : Module.Dual ℤ (LinearMap.ker (phiBar N))) : χ = 0 := by

  obtain ⟨m, c, hm⟩ := exists_basis_periodLattice_card_eq N
  obtain ⟨n, b, hn⟩ := exists_basis_parabolicHoms_card_le N
  have hnm : n ≤ m := hm ▸ hn
  haveI : Module.Free ℤ (ModularCurve.periodLattice N) := Module.Free.of_basis c
  haveI : Module.Finite ℤ (ModularCurve.periodLattice N) := Module.Finite.of_basis c

  obtain ⟨sec, hsec⟩ := (phiBar N).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (phiBar_surjective N))

  set K := LinearMap.ker (phiBar N) with hK
  have hsecapp : ∀ y, phiBar N (sec y) = y := fun y => by
    have := congrArg (fun f => f y) hsec
    simpa using this
  let split : Q N →ₗ[ℤ] ModularCurve.periodLattice N × K :=
    LinearMap.prod (phiBar N)
      (LinearMap.codRestrict K (LinearMap.id - sec ∘ₗ phiBar N) (fun x => by
        simp [hK, LinearMap.mem_ker, map_sub, hsecapp]))
  let unsplit : ModularCurve.periodLattice N × K →ₗ[ℤ] Q N :=
    sec ∘ₗ LinearMap.fst ℤ _ _ + K.subtype ∘ₗ LinearMap.snd ℤ _ _
  have h1 : ∀ x, unsplit (split x) = x := fun x => by
    simp [split, unsplit]
  have h2 : ∀ y, split (unsplit y) = y := by
    rintro ⟨y, k⟩
    have hk : phiBar N (k : Q N) = 0 := k.2
    apply Prod.ext
    · simp [split, unsplit, hsecapp, hk]
    · apply Subtype.ext
      simp [split, unsplit, hsecapp, hk]
  let e : Q N ≃ₗ[ℤ] ModularCurve.periodLattice N × K :=
    { split with invFun := unsplit, left_inv := h1, right_inv := h2 }

  let eD : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ ≃ₗ[ℤ]
      Module.Dual ℤ (ModularCurve.periodLattice N) × Module.Dual ℤ K :=
    (dualEquiv N).trans (e.symm.dualMap.trans (Module.dualProdDualEquivDual ℤ _ _).symm)

  haveI : Module.Finite ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) :=
    Module.Finite.of_basis b
  haveI : Module.Free ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) :=
    Module.Free.of_basis b
  haveI : Module.Finite ℤ (Module.Dual ℤ K) :=
    Module.Finite.of_surjective
      ((LinearMap.snd ℤ (Module.Dual ℤ (ModularCurve.periodLattice N)) (Module.Dual ℤ K)).comp
        eD.toLinearMap)
      (fun χ => ⟨eD.symm (0, χ), by simp⟩)
  haveI : Module.Free ℤ (Module.Dual ℤ K) := inferInstance
  haveI : Module.Free ℤ (Module.Dual ℤ (ModularCurve.periodLattice N)) :=
    Module.Free.of_basis c.dualBasis
  haveI : Module.Finite ℤ (Module.Dual ℤ (ModularCurve.periodLattice N)) :=
    Module.Finite.of_basis c.dualBasis

  have hP : Module.finrank ℤ
      (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hΛ : Module.finrank ℤ (Module.Dual ℤ (ModularCurve.periodLattice N)) = m := by
    rw [Module.finrank_eq_card_basis c.dualBasis, Fintype.card_fin]
  have hsum := eD.finrank_eq
  rw [Module.finrank_prod, hP, hΛ] at hsum
  have hK0 : Module.finrank ℤ (Module.Dual ℤ K) = 0 := by omega
  have hsub : Subsingleton (Module.Dual ℤ K) := Module.finrank_zero_iff.mp hK0
  exact Subsingleton.elim _ _

end CpairK2
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period.CpairK2"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period.CpairK2"

theorem solution (N : ℕ) [NeZero N] :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ ≃ₗ[ℤ]
        Module.Dual ℤ (ModularCurve.periodLattice N),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
        (δ : CongruenceSubgroup.Gamma0 N),
        EV ψ ⟨ModularCurve.period N δ, ModularCurve.period_mem_periodLattice N δ⟩ =
          (ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ) (Additive.ofMul δ) := by
  open CpairK2 in
  obtain ⟨m, c, -⟩ := exists_basis_periodLattice_card_eq N
  haveI : Module.Free ℤ (ModularCurve.periodLattice N) := Module.Free.of_basis c
  obtain ⟨sec, hsec⟩ := (phiBar N).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (phiBar_surjective N))
  have hsecapp : ∀ y, phiBar N (sec y) = y := fun y => by
    have := congrArg (fun f => f y) hsec
    simpa using this

  have key : ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ) (x : Q N),
      barOf N ψ x = barOf N ψ (sec (phiBar N x)) := by
    intro ψ x
    have hx : x - sec (phiBar N x) ∈ LinearMap.ker (phiBar N) := by
      rw [LinearMap.mem_ker, map_sub, hsecapp, sub_self]
    have h0 := dual_ker_phiBar_eq_zero N ((barOf N ψ).comp (LinearMap.ker (phiBar N)).subtype)
    have := congrArg (fun f => f ⟨_, hx⟩) h0
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, map_sub,
      LinearMap.zero_apply] at this
    linarith
  let EV₀ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ →ₗ[ℤ]
      Module.Dual ℤ (ModularCurve.periodLattice N) :=
    sec.dualMap ∘ₗ (dualEquiv N).toLinearMap
  have hEV₀ : ∀ ψ y, EV₀ ψ y = barOf N ψ (sec y) := fun ψ y => rfl
  have hval : ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
      (δ : CongruenceSubgroup.Gamma0 N),
      EV₀ ψ (perΛ N δ) = (ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ) (Additive.ofMul δ) := by
    intro ψ δ
    rw [hEV₀, ← phiBar_cls, ← key, barOf_cls]
  have hinj : Function.Injective EV₀ := by
    intro ψ ψ' h
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    have h1 := hval ψ (Additive.toMul x)
    have h2 := hval ψ' (Additive.toMul x)
    rw [h] at h1
    rw [ofMul_toMul] at h1 h2
    rw [← h1, ← h2]
  have hsurj : Function.Surjective EV₀ := by
    intro μ
    refine ⟨ofBar N (μ ∘ₗ phiBar N), ?_⟩
    apply LinearMap.ext_on_range (span_perΛ N)
    intro δ
    rw [hval, ofBar_apply, LinearMap.comp_apply, phiBar_cls]
  refine ⟨LinearEquiv.ofBijective EV₀ ⟨hinj, hsurj⟩, fun ψ δ => ?_⟩
  rw [LinearEquiv.ofBijective_apply]
  exact hval ψ δ

end S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period
end P2MW
export P2MW.S_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLattice_apply_period (solution)
