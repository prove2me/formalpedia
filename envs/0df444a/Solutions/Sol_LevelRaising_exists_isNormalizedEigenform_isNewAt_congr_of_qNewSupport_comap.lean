-- Prove2me | solution 1 for LevelRaising.exists_isNormalizedEigenform_isNewAt_congr_of_qNewSupport_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fdb2fc9e-6321-56be-b1ab-d4192b84b0ee

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_FreyPackage_LevelRaising
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support
import Theorems.Thm_CuspForm_exists_conj_isNormalizedEigenform_isNewAt
import Theorems.Thm_integralClosure_exists_complex_ringEquiv_apply_eq
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Algebraic.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LevelRaising_exists_isNormalizedEigenform_isNewAt_congr_of_qNewSupport_comap
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option Elab.async false

namespace SolCW

section ZbarQuotAlgClosed

open Polynomial

theorem exists_root_of_monic_of_surjective {k : Type*} [CommRing k]
    (ψ : (integralClosure ℤ ℂ) →+* k) (hsurj : Function.Surjective ψ)
    {p : Polynomial k} (hp : p.Monic) (hdeg : p.natDegree ≠ 0) :
    ∃ x : k, p.eval x = 0 := by
  have hlifts : p ∈ Polynomial.lifts ψ :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr fun n => hsurj (p.coeff n)
  obtain ⟨q, hq_map, hq_deg, hq_monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hdegC : (q.map (algebraMap (integralClosure ℤ ℂ) ℂ)).degree ≠ 0 := by
    intro h0
    apply hdeg
    rw [← hq_deg, ← hq_monic.natDegree_map (algebraMap (integralClosure ℤ ℂ) ℂ)]
    exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (q.map (algebraMap (integralClosure ℤ ℂ) ℂ)) hdegC
  have hα0 : (q.map (algebraMap (integralClosure ℤ ℂ) ℂ)).eval α = 0 := hα
  have hint : IsIntegral (integralClosure ℤ ℂ) α :=
    ⟨q, hq_monic, by rwa [← Polynomial.eval_map]⟩
  have hintZ : IsIntegral ℤ α := isIntegral_trans α hint
  have hq_eval : q.eval (⟨α, hintZ⟩ : integralClosure ℤ ℂ) = 0 := by
    have h1 : algebraMap (integralClosure ℤ ℂ) ℂ (q.eval ⟨α, hintZ⟩) = 0 := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
      exact hα0
    exact Subtype.val_injective
      (h1.trans (map_zero (algebraMap (integralClosure ℤ ℂ) ℂ)).symm)
  refine ⟨ψ ⟨α, hintZ⟩, ?_⟩
  have hpush : p.eval (ψ ⟨α, hintZ⟩) = ψ (q.eval ⟨α, hintZ⟩) := by
    rw [← hq_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [hpush, hq_eval, map_zero]

theorem isAlgClosed_of_surjective {k : Type*} [Field k]
    (ψ : (integralClosure ℤ ℂ) →+* k) (hsurj : Function.Surjective ψ) :
    IsAlgClosed k := by
  refine IsAlgClosed.of_exists_root (k := k) fun p hmonic hirr => ?_
  refine exists_root_of_monic_of_surjective ψ hsurj hmonic fun h0 => hirr.ne_one ?_
  exact hmonic.degree_le_zero_iff_eq_one.mp
    (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp h0)

theorem isAlgClosed_quotient (𝔪 : Ideal (integralClosure ℤ ℂ)) [𝔪.IsMaximal] :
    @IsAlgClosed ((integralClosure ℤ ℂ) ⧸ 𝔪) (Ideal.Quotient.field 𝔪) := by
  letI : Field ((integralClosure ℤ ℂ) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  exact isAlgClosed_of_surjective (Ideal.Quotient.mk 𝔪) Ideal.Quotient.mk_surjective

end ZbarQuotAlgClosed

section CharExtension

theorem exists_ringHom_extend_of_isIntegral {S A F : Type*} [CommRing S] [CommRing A]
    [Algebra S A] [Algebra.IsIntegral S A] [Field F] [IsAlgClosed F]
    (hinj : Function.Injective (algebraMap S A)) (θ₀ : S →+* F) :
    ∃ θ : A →+* F, ∀ s : S, θ (algebraMap S A s) = θ₀ s := by
  classical
  haveI : (RingHom.ker θ₀).IsPrime := RingHom.ker_isPrime θ₀
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker θ₀)
    (⊥ : Ideal A) (by
      intro s hs
      rw [Ideal.mem_comap, Ideal.mem_bot] at hs
      have : s = 0 := hinj (by rw [hs, map_zero])
      simp [this])
  haveI := hQp
  have hp : ∀ a ∈ Q.comap (algebraMap S A), θ₀ a = 0 := fun a ha => by
    rw [hQ] at ha; exact ha
  let ι : S ⧸ Q.comap (algebraMap S A) →+* F := Ideal.Quotient.lift _ θ₀ hp
  have hι : Function.Injective ι :=
    RingHom.lift_injective_of_ker_le_ideal _ hp (by rw [hQ])
  letI : Algebra (S ⧸ Q.comap (algebraMap S A)) F := ι.toAlgebra
  haveI : Module.IsTorsionFree (S ⧸ Q.comap (algebraMap S A)) F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  haveI : Module.IsTorsionFree (S ⧸ Q.comap (algebraMap S A)) (A ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  let ψ : (A ⧸ Q) →ₐ[S ⧸ Q.comap (algebraMap S A)] F := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), fun s => ?_⟩
  have e2 : Ideal.Quotient.mk Q (algebraMap S A s) =
      algebraMap (S ⧸ Q.comap (algebraMap S A)) (A ⧸ Q) (Ideal.Quotient.mk _ s) := rfl
  calc ψ.toRingHom.comp (Ideal.Quotient.mk Q) (algebraMap S A s)
      = ψ (algebraMap (S ⧸ Q.comap (algebraMap S A)) (A ⧸ Q) (Ideal.Quotient.mk _ s)) := by
        rw [RingHom.comp_apply, e2]; rfl
    _ = algebraMap (S ⧸ Q.comap (algebraMap S A)) F (Ideal.Quotient.mk _ s) := ψ.commutes _
    _ = θ₀ s := Ideal.Quotient.lift_mk _ θ₀ hp

theorem exists_ringHom_comp_eq {H : Type*} [CommRing H]
    (χ χ₁ : H →+* integralClosure ℤ ℂ) (𝔪 : Ideal (integralClosure ℤ ℂ)) [𝔪.IsMaximal]
    (hker : RingHom.ker χ ≤ Ideal.comap χ₁ 𝔪) :
    ∃ θ : integralClosure ℤ ℂ →+* integralClosure ℤ ℂ ⧸ 𝔪,
      ∀ T, θ (χ T) = Ideal.Quotient.mk 𝔪 (χ₁ T) := by
  classical
  letI instF : Field (integralClosure ℤ ℂ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : IsAlgClosed (integralClosure ℤ ℂ ⧸ 𝔪) := isAlgClosed_quotient 𝔪

  have hsurj : Function.Surjective χ.rangeRestrict := χ.rangeRestrict_surjective
  have hker' : RingHom.ker χ.rangeRestrict ≤ RingHom.ker ((Ideal.Quotient.mk 𝔪).comp χ₁) := by
    intro T hT
    rw [RingHom.mem_ker] at hT ⊢
    have hT' : χ T = 0 := congrArg Subtype.val hT
    have h2 : T ∈ Ideal.comap χ₁ 𝔪 := hker (by rwa [RingHom.mem_ker])
    simpa [Ideal.Quotient.eq_zero_iff_mem] using h2
  let θ₀ : χ.range →+* integralClosure ℤ ℂ ⧸ 𝔪 :=
    χ.rangeRestrict.liftOfSurjective hsurj ⟨_, hker'⟩
  have hθ₀ : ∀ T, θ₀ (χ.rangeRestrict T) = Ideal.Quotient.mk 𝔪 (χ₁ T) := fun T =>
    χ.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨_, hker'⟩ T

  haveI : Algebra.IsIntegral χ.range (integralClosure ℤ ℂ) :=
    ⟨fun x => (integralClosure.isIntegral x).tower_top⟩
  have hinj : Function.Injective (algebraMap χ.range (integralClosure ℤ ℂ)) :=
    Subtype.val_injective
  obtain ⟨θ, hθ⟩ := exists_ringHom_extend_of_isIntegral hinj θ₀
  refine ⟨θ, fun T => ?_⟩
  have e1 : χ T = algebraMap χ.range (integralClosure ℤ ℂ) (χ.rangeRestrict T) := rfl
  rw [e1, hθ, hθ₀]

end CharExtension

end SolCW

set_option maxHeartbeats 3200000 in
theorem solution
    {M q' : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q') (hq' : q'.Prime)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hmax : 𝔪.IsMaximal)
    (χ₁ : CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M} →+* integralClosure ℤ ℂ)
    (hsupp : ∀ T : CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M},
        (∀ g ∈ LinearMap.ker (CuspForm.traceLin A hq')
              ⊓ LinearMap.ker ((CuspForm.traceLin A hq') ∘ₗ (CuspForm.atkinLehnerLin A 2)),
          (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) g = 0)
          → T ∈ Ideal.comap χ₁ 𝔪) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2,
      g.IsNormalizedEigenform ∧ CuspForm.IsNewAt g q' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
        ∃ b : integralClosure ℤ ℂ, (b : ℂ) = ModularFormClass.qCoeff g ℓ ∧
          χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) - b ∈ 𝔪 := by

  haveI : 𝔪.IsPrime := hmax.isPrime
  haveI h𝔭 : (Ideal.comap χ₁ 𝔪).IsPrime := Ideal.IsPrime.comap χ₁

  obtain ⟨f, hf, χ, hχ, hker, haq⟩ :=
    CuspForm.exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support A hq'
      (Ideal.comap χ₁ 𝔪) h𝔭 hsupp

  haveI : 𝔪.IsMaximal := hmax
  obtain ⟨θ, hθ⟩ := SolCW.exists_ringHom_comp_eq χ χ₁ 𝔪 hker

  letI kF : Field (integralClosure ℤ ℂ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let θ' : integralClosure ℤ ℂ →+* integralClosure ℤ ℂ ⧸ 𝔪 :=
    { toFun := θ, map_one' := θ.map_one, map_mul' := θ.map_mul,
      map_zero' := θ.map_zero, map_add' := θ.map_add }
  let mk' : integralClosure ℤ ℂ →+* integralClosure ℤ ℂ ⧸ 𝔪 :=
    { toFun := Ideal.Quotient.mk 𝔪, map_one' := (Ideal.Quotient.mk 𝔪).map_one,
      map_mul' := (Ideal.Quotient.mk 𝔪).map_mul, map_zero' := (Ideal.Quotient.mk 𝔪).map_zero,
      map_add' := (Ideal.Quotient.mk 𝔪).map_add }
  obtain ⟨σ, hσ⟩ :=
    integralClosure.exists_complex_ringEquiv_apply_eq (integralClosure ℤ ℂ ⧸ 𝔪) θ' mk'

  obtain ⟨g, hg, hgnew, hgcoef⟩ :=
    CuspForm.exists_conj_isNormalizedEigenform_isNewAt M σ f hf q' haq
  refine ⟨g, hg, hgnew, ?_⟩
  intro ℓ hℓ hℓM

  have hbint : IsIntegral ℤ (σ ((χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ))) := by
    have h0 : IsIntegral ℤ ((χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ)) :=
      (χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM)).2
    exact h0.map σ.toRingHom.toIntAlgHom
  refine ⟨⟨σ ((χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ)), hbint⟩, ?_, ?_⟩
  ·
    show σ ((χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ)) = ModularFormClass.qCoeff g ℓ
    rw [hgcoef ℓ, ← hχ ℓ hℓ hℓM]
  ·
    have h1 : θ (χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM)) =
        Ideal.Quotient.mk 𝔪 ⟨σ ((χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ)), hbint⟩ :=
      hσ _ _ rfl
    have h2 : θ (χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM)) =
        Ideal.Quotient.mk 𝔪 (χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM)) := hθ _
    exact Ideal.Quotient.eq.mp (h2.symm.trans h1)

end S_LevelRaising_exists_isNormalizedEigenform_isNewAt_congr_of_qNewSupport_comap
end P2MW
export P2MW.S_LevelRaising_exists_isNormalizedEigenform_isNewAt_congr_of_qNewSupport_comap (solution)
