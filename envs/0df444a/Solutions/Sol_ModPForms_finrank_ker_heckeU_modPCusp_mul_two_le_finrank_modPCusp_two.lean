-- Prove2me | solution 1 for ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ec699a9c-650e-5da6-98a6-370b8a670127

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg
import Theorems.Thm_LinearMap_finrank_ker_baseChange_le_padicValInt_det
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_intLattice_free_and_finite
import Theorems.Thm_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU
import Theorems.Thm_CuspForm_linearIndependent_of_mem_intLattice
import Theorems.Thm_ModPForms_card_le_finrank_modPCusp_of_linearIndependent
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL"
p2m_attr_erase "simp" "HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply"
p2m_attr_erase "simp" "ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
set_option autoImplicit false

namespace ModPCuspHeckeUKerAux

open scoped TensorProduct

variable {M : ℕ}

private theorem linearIndependent_int_val {ι : Type} (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) :
    LinearIndependent ℤ (fun i => (b i : CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
  b.linearIndependent.map' (CuspForm.intLattice M 2).subtype (Submodule.ker_subtype _)

private theorem linearIndependent_complex_val [NeZero M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) :
    LinearIndependent ℂ (fun i => (b i : CuspForm (CongruenceSubgroup.Gamma0 M) 2)) := by
  have h := CuspForm.linearIndependent_of_mem_intLattice (Fintype.card ι)
    (fun j => (b ((Fintype.equivFin ι).symm j) : CuspForm (CongruenceSubgroup.Gamma0 M) 2))
    (fun j => (b _).2) ((linearIndependent_int_val b).comp _ (Fintype.equivFin ι).symm.injective)
  have h' := h.comp _ (Fintype.equivFin ι).injective
  convert h' using 1
  ext i
  simp

private theorem span_complex_val [NeZero M] {ι : Type} (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => (b i : CuspForm (CongruenceSubgroup.Gamma0 M) 2)) := by
  have hIS : Submodule.span ℂ ((CuspForm.intLattice M 2 : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :
      Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) = ⊤ := CuspForm.hasIntegralStructure_two M
  rw [← hIS, Submodule.span_le]
  intro f hf
  have hmem : (⟨f, hf⟩ : ↥(CuspForm.intLattice M 2)) ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]; trivial
  have hmap := Submodule.mem_map_of_mem (f := (CuspForm.intLattice M 2).subtype) hmem
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  exact Submodule.span_le_restrictScalars ℤ ℂ _ hmap

private noncomputable def basisC [NeZero M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) :
    Module.Basis ι ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  Module.Basis.mk (linearIndependent_complex_val b) (span_complex_val b)

@[scoped simp] private theorem basisC_apply [NeZero M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) (i : ι) :
    basisC b i = (b i : CuspForm (CongruenceSubgroup.Gamma0 M) 2) := by
  simp [basisC]

private noncomputable def redMap (F : Type) [Field F]
    (a : ↥(CuspForm.intLattice M 2) →+ (ℕ → ℤ)) : ↥(CuspForm.intLattice M 2) →ₗ[ℤ] PowerSeries F :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => PowerSeries.mk fun n => ((a f n : ℤ) : F)
      map_zero' := by ext n; simp
      map_add' := fun f g => by ext n; simp }

@[scoped simp] private theorem coeff_redMap (F : Type) [Field F]
    (a : ↥(CuspForm.intLattice M 2) →+ (ℕ → ℤ)) (f : ↥(CuspForm.intLattice M 2)) (n : ℕ) :
    PowerSeries.coeff n (redMap F a f) = ((a f n : ℤ) : F) := by
  simp [redMap]

private theorem range_eq_modPCusp (F : Type) [Field F]
    (a : ↥(CuspForm.intLattice M 2) →+ (ℕ → ℤ))
    (ha : ∀ (f : ↥(CuspForm.intLattice M 2)) (n : ℕ),
      ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) n) :
    LinearMap.range ((redMap F a).liftBaseChange F) = ModPForms.modPCusp M 2 F := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      rw [LinearMap.liftBaseChange_tmul]
      refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(f : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
        a f, fun n => (ha f n).symm, ?_⟩)
      ext n
      simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [ModPForms.modPCusp, Submodule.span_le]
    rintro φ ⟨f, c, hc, rfl⟩
    have hf : f ∈ CuspForm.intLattice M 2 := Submodule.subset_span fun n => ⟨c n, hc n⟩
    refine ⟨(1 : F) ⊗ₜ ⟨f, hf⟩, ?_⟩
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    ext n
    rw [coeff_redMap, PowerSeries.coeff_mk]
    have h := (ha ⟨f, hf⟩ n).trans (hc n)
    exact_mod_cast congrArg (fun z : ℤ => (z : F)) (Int.cast_injective h)

private theorem card_le_finrank_modPCusp [NeZero M] (F : Type) [Field F] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2))
    (a : ↥(CuspForm.intLattice M 2) →+ (ℕ → ℤ))
    (ha : ∀ (f : ↥(CuspForm.intLattice M 2)) (n : ℕ),
      ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) n) :
    Fintype.card ι ≤ Module.finrank F ↥(ModPForms.modPCusp M 2 F) :=
  ModPForms.card_le_finrank_modPCusp_of_linearIndependent M 2 F
    (fun i => (b i : CuspForm (CongruenceSubgroup.Gamma0 M) 2)) (fun i => a (b i))
    (fun i n => (ha (b i) n).symm) (linearIndependent_complex_val b)

private theorem finrank_modPCusp_eq [NeZero M] (F : Type) [Field F] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(CuspForm.intLattice M 2)) :
    Module.finrank F ↥(ModPForms.modPCusp M 2 F) = Fintype.card ι := by
  obtain ⟨a, ha, -, -⟩ := CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated M 2
  haveI : Module.Free ℤ ↥(CuspForm.intLattice M 2) := Module.Free.of_basis b
  haveI : Module.Finite ℤ ↥(CuspForm.intLattice M 2) := Module.Finite.of_basis b
  refine le_antisymm ?_ (card_le_finrank_modPCusp F b a ha)
  rw [← range_eq_modPCusp F a ha]
  refine (LinearMap.finrank_range_le _).trans (le_of_eq ?_)
  rw [Module.finrank_baseChange, Module.finrank_eq_card_basis b]

end ModPCuspHeckeUKerAux
p2m_reactivate "P2MW.S_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two.ModPCuspHeckeUKerAux"

open ModPCuspHeckeUKerAux in
open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (F : Type) [Field F] :
    Module.finrank F
        ↥(LinearMap.ker ((PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F).domRestrict
          (ModPForms.modPCusp (N * p) 2 F)))
      ≤ Module.finrank F ↥(ModPForms.modPCusp N 2 F) := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) hp0⟩
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2) :=
    CuspForm.finiteDimensional_Gamma0 (N * p) 2
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2

  obtain ⟨hfree, hfin⟩ := CuspForm.intLattice_free_and_finite (N * p) 2
  obtain ⟨hfreeN, hfinN⟩ := CuspForm.intLattice_free_and_finite N 2
  let b := Module.Free.chooseBasis ℤ ↥(CuspForm.intLattice (N * p) 2)
  let bN := Module.Free.chooseBasis ℤ ↥(CuspForm.intLattice N 2)

  let U : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2 :=
    CuspForm.heckeULin 2 (dvd_mul_left p N)
  have hUL : ∀ f ∈ CuspForm.intLattice (N * p) 2,
      (U.restrictScalars ℤ) f ∈ CuspForm.intLattice (N * p) 2 :=
    fun f hf => CuspForm.mem_intLattice_of_coe_eq_heckeU hp0
      (CuspForm.coe_heckeULin_apply 2 (dvd_mul_left p N) f) hf
  let A : ↥(CuspForm.intLattice (N * p) 2) →ₗ[ℤ] ↥(CuspForm.intLattice (N * p) 2) :=
    (U.restrictScalars ℤ).restrict hUL
  have hA : ∀ f : ↥(CuspForm.intLattice (N * p) 2),
      ((A f : ↥(CuspForm.intLattice (N * p) 2)) : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2) = U f :=
    fun f => rfl

  obtain ⟨a, ha, hainj, -⟩ := CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated (N * p) 2
  have haA : ∀ (f : ↥(CuspForm.intLattice (N * p) 2)) (n : ℕ), a (A f) n = a f (p * n) := by
    intro f n
    apply Int.cast_injective (α := ℂ)
    rw [ha (A f) n, hA f, CuspForm.coe_heckeULin_apply,
      ModularFormClass.qCoeff_heckeU (f : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2)
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N * p)) hp0,
      ModularForm.coeffHeckeU_apply, ha f, Nat.mul_comm n p]
  let Ψ : F ⊗[ℤ] ↥(CuspForm.intLattice (N * p) 2) →ₗ[F] PowerSeries F := (redMap F a).liftBaseChange F

  have hequiv : Ψ ∘ₗ (A.baseChange F) = (PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F) ∘ₗ Ψ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c f
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
      LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
    ext n
    rw [coeff_redMap, PowerSeries.coeff_heckeU, coeff_redMap, haA]

  have hrange : LinearMap.range Ψ = ModPForms.modPCusp (N * p) 2 F := range_eq_modPCusp F a ha
  have hdim : Module.finrank F ↥(ModPForms.modPCusp (N * p) 2 F) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(CuspForm.intLattice (N * p) 2)) := finrank_modPCusp_eq F b
  have hdimN : Module.finrank F ↥(ModPForms.modPCusp N 2 F) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(CuspForm.intLattice N 2)) := finrank_modPCusp_eq F bN
  have hdimNC : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) =
      Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(CuspForm.intLattice N 2)) :=
    Module.finrank_eq_card_basis (basisC bN)
  have hΨinj : Function.Injective Ψ := by
    have H : Module.finrank F (F ⊗[ℤ] ↥(CuspForm.intLattice (N * p) 2)) =
        Module.finrank F ↥(LinearMap.range Ψ) := by
      rw [hrange, hdim, Module.finrank_baseChange, Module.finrank_eq_card_basis b]
    rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_rangeRestrict, LinearMap.ker_eq_bot]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mpr (LinearMap.surjective_rangeRestrict _)

  have hker : Module.finrank F
      ↥(LinearMap.ker ((PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F).domRestrict
        (ModPForms.modPCusp (N * p) 2 F))) = Module.finrank F ↥(LinearMap.ker (A.baseChange F)) := by
    let e : F ⊗[ℤ] ↥(CuspForm.intLattice (N * p) 2) ≃ₗ[F] ↥(ModPForms.modPCusp (N * p) 2 F) :=
      (LinearEquiv.ofInjective Ψ hΨinj).trans (LinearEquiv.ofEq _ _ hrange)
    have he : ∀ x, ((e x : ↥(ModPForms.modPCusp (N * p) 2 F)) : PowerSeries F) = Ψ x := fun x => rfl
    have hequiv' : ∀ x, Ψ (A.baseChange F x) =
        (PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F) (Ψ x) := fun x => LinearMap.congr_fun hequiv x
    have hmap : (LinearMap.ker (A.baseChange F)).map (e : _ →ₗ[F] _) =
        LinearMap.ker ((PowerSeries.heckeU p : PowerSeries F →ₗ[F] PowerSeries F).domRestrict
          (ModPForms.modPCusp (N * p) 2 F)) := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [LinearEquiv.coe_coe, he, ← hequiv' x, hx, map_zero]
      · intro hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        apply hΨinj
        rw [map_zero, hequiv', ← he, e.apply_symm_apply, hy]
    exact (LinearEquiv.ofSubmodules e _ _ hmap).finrank_eq.symm

  have hdetA : LinearMap.det A = (p : ℤ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ∨
      LinearMap.det A = -(p : ℤ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
    have hmat : LinearMap.toMatrix (basisC b) (basisC b) U = (LinearMap.toMatrix b b A).map (Int.castRingHom ℂ) := by
      ext i j
      rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, basisC_apply, ← hA]
      have hsum := congrArg (fun x : ↥(CuspForm.intLattice (N * p) 2) =>
        (x : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2)) (b.sum_repr (A (b j)))
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
      rw [← hsum]
      simp only [← basisC_apply (b := b), ← Int.cast_smul_eq_zsmul ℂ]
      rw [(basisC b).repr_sum_self]
      simp
    have hdet : LinearMap.det U = ((LinearMap.det A : ℤ) : ℂ) := by
      rw [← LinearMap.det_toMatrix (basisC b), hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        LinearMap.det_toMatrix]
      rfl
    rcases CuspForm.det_heckeULin_two_eq_pow_finrank_or_eq_neg p N hpN with h | h
    · left
      apply Int.cast_injective (α := ℂ)
      rw [← hdet]
      exact_mod_cast h
    · right
      apply Int.cast_injective (α := ℂ)
      rw [← hdet]
      exact_mod_cast h

  rw [hker, hdimN, ← hdimNC]
  haveI : Module.Free ℤ ↥(CuspForm.intLattice (N * p) 2) := hfree
  haveI : Module.Finite ℤ ↥(CuspForm.intLattice (N * p) 2) := hfin
  have hdet0 : LinearMap.det A ≠ 0 := by
    rcases hdetA with h | h <;> simp [h, hp.ne_zero]
  by_cases hchar : ringChar F = p
  · haveI : CharP F p := hchar ▸ (inferInstance : CharP F (ringChar F))
    refine (LinearMap.finrank_ker_baseChange_le_padicValInt_det A hdet0 p F).trans (le_of_eq ?_)
    rcases hdetA with h | h <;> simp [h, padicValInt, Int.natAbs_pow, padicValNat.prime_pow]
  · have hpF : (p : F) ≠ 0 := fun h0 => hchar (CharP.ringChar_of_prime_eq_zero hp h0)
    have hunit : IsUnit (LinearMap.det (A.baseChange F)) := by
      rw [LinearMap.det_baseChange, isUnit_iff_ne_zero]
      rcases hdetA with h | h <;> simp [h, hpF]
    have hkb : LinearMap.ker (A.baseChange F) = ⊥ :=
      (LinearMap.isUnit_iff_ker_eq_bot _).mp ((LinearMap.isUnit_iff_isUnit_det _).mpr hunit)
    rw [hkb, finrank_bot]
    exact Nat.zero_le _

end S_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
end P2MW
export P2MW.S_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two (solution)
