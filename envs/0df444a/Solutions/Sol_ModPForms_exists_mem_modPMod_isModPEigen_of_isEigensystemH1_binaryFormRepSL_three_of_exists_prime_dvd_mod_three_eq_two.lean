-- Prove2me | solution 1 for ModPForms.exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/736e380b-f5cd-58f6-9195-777356a4d431

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL
import Theorems.Thm_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
import Theorems.Thm_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1
import Theorems.Thm_ModularForm_span_setOf_qCoeff_intCast_eq_top
import Theorems.Thm_ModularForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularForm_heckeTLin_comm
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom
import Theorems.Thm_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero CohCarrier.conjUpperMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

namespace C3ES

open CongruenceSubgroup HeckeEis ModularFormClass
open scoped MatrixGroups TensorProduct

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

@[scoped simp] theorem heckeLin_apply (z : Gamma0 N → V) : heckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

theorem eq_heckeH1_of_isCoeffHeckeOnH1 (ha : IsCompat N ℓ ρ a) {T : coeffH1 ρ →ₗ[K] coeffH1 ρ}
    (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) : T = heckeH1 ha :=
  unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_heckeH1 ha)

theorem coeffH1Mk_eq_iff (z w : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = coeffH1Mk ρ w ↔ (z : Gamma0 N → V) - w ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.eq _).trans Submodule.mem_comap

theorem heckeH1_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (hne : ℓ ≠ ℓ') {a a' : V →ₗ[K] V}
    (ha : IsCompat N ℓ ρ a) (ha' : IsCompat N ℓ' ρ a') (hcomm : a ∘ₗ a' = a' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (heckeH1 ha' x) = heckeH1 ha' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [heckeH1_mk, heckeH1_mk, heckeH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]
  simp only [coe_heckeZ1]
  haveI : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  have hℓℓ' : ¬ ℓ ∣ ℓ' := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp h)
  have hℓ'ℓ : ¬ ℓ' ∣ ℓ := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ' hℓ).mp h).symm
  have h1 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ ℓ' (ℓ * ℓ')
    hℓ hℓN hℓℓ' rfl ρ a a' ha ha' z.2
  have h2 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ' ℓ (ℓ * ℓ')
    hℓ' hℓ'N hℓ'ℓ (Nat.mul_comm ℓ ℓ') ρ a' a ha' ha z.2
  rw [← hcomm] at h2
  have h3 := (coeffCoboundaries ρ).sub_mem h1 h2
  convert h3 using 1
  abel

end Induced

section Sym

variable (R : Type) [CommRing R] (N : ℕ) (n : ℕ)

noncomputable abbrev ρSym : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

def dMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

theorem dMat_comm (ℓ ℓ' : ℕ) : dMat ℓ * dMat ℓ' = dMat ℓ' * dMat ℓ := by
  simp only [dMat, Matrix.mul_fin_two]
  congr 1 <;> ring

theorem binaryFormAlphaAdj_eq (ℓ : ℕ) : binaryFormAlphaAdj R n ℓ = binaryFormRep R n (dMat ℓ) := rfl

theorem isCompat_sym (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj R n N ℓ u

theorem alpha_comm (ℓ ℓ' : ℕ) :
    binaryFormAlphaAdj R n ℓ ∘ₗ binaryFormAlphaAdj R n ℓ' =
      binaryFormAlphaAdj R n ℓ' ∘ₗ binaryFormAlphaAdj R n ℓ := by
  rw [binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq]
  change binaryFormRep R n (dMat ℓ) * binaryFormRep R n (dMat ℓ') =
    binaryFormRep R n (dMat ℓ') * binaryFormRep R n (dMat ℓ)
  rw [← map_mul, ← map_mul, dMat_comm]

abbrev H1 : Type := coeffH1 (ρSym R N n)

noncomputable def TH (ℓ : ℕ) [NeZero ℓ] : H1 R N n →ₗ[R] H1 R N n :=
  heckeH1 (isCompat_sym R N n ℓ)

theorem isCoeffHeckeOnH1_TH (ℓ : ℕ) [NeZero ℓ] :
    IsCoeffHeckeOnH1 N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) (TH R N n ℓ) :=
  isCoeffHeckeOnH1_heckeH1 _

theorem TH_mk (ℓ : ℕ) [NeZero ℓ] (z : ↥(coeffCocycles (ρSym R N n))) :
    TH R N n ℓ (coeffH1Mk _ z) = coeffH1Mk _ (heckeZ1 (isCompat_sym R N n ℓ) z) := rfl

theorem eq_TH {ℓ : ℕ} [NeZero ℓ] {T : H1 R N n →ₗ[R] H1 R N n}
    (hT : IsCoeffHeckeOnH1 N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) T) : T = TH R N n ℓ :=
  eq_heckeH1_of_isCoeffHeckeOnH1 _ hT

theorem TH_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) : Commute (TH R N n ℓ) (TH R N n ℓ') := by
  by_cases hne : ℓ = ℓ'
  · subst hne; exact Commute.refl _
  refine LinearMap.ext fun x => ?_
  exact heckeH1_comm hℓ hℓ' hℓN hℓ'N hne (isCompat_sym R N n ℓ) (isCompat_sym R N n ℓ')
    (alpha_comm R n ℓ ℓ') x

end Sym

section FiniteDim

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_apply_eq_zero_of_closure {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  have h1 : (z : G → V) 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    rw [mul_inv_cancel, h1, ih, zero_add] at h
    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

theorem finiteDimensional_coeffH1 (N : ℕ) [NeZero N] [FiniteDimensional K V]
    (ρ : Representation K (Gamma0 N) V) : FiniteDimensional K (coeffH1 ρ) := by
  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
      Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out
  let ev : ↥(coeffCocycles ρ) →ₗ[K] (↥S → V) :=
    { toFun := fun z s => (z : Gamma0 N → V) s
      map_add' := fun z w => by ext s; rfl
      map_smul' := fun c z => by ext s; rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (funext fun g => ?_)
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure ρ z S (fun s hs => congrFun hz ⟨s, hs⟩) g hg
  haveI : FiniteDimensional K ↥(coeffCocycles ρ) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (coeffH1Mk ρ) (coeffH1Mk_surjective ρ)

scoped instance finiteDimensional_binaryForm (n : ℕ) : FiniteDimensional K ↥(BinaryForm K n) := by
  have hle : BinaryForm K n ≤ MvPolynomial.restrictTotalDegree (Fin 2) K n := fun φ hφ =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule n φ).mp hφ).totalDegree_le
  exact Submodule.finiteDimensional_of_le hle

end FiniteDim

section Words

variable {ι : Type}

noncomputable abbrev ev {A : Type*} [Ring A] (t : ι → A) : FreeAlgebra ℤ ι →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ t

theorem ev_algebraMap {A : Type*} [Ring A] (t : ι → A) (r : ℤ) :
    ev t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

theorem map_ev_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {A B : Type*} [Ring A] [Ring B] [Module A X] [Module B Y]
    (t : ι → A) (t' : ι → B) (Φ : X →+ Y) (hΦ : ∀ i x, Φ (t i • x) = t' i • Φ x)
    (w : FreeAlgebra ℤ ι) (x : X) : Φ (ev t w • x) = ev t' w • Φ x := by
  induction w using FreeAlgebra.induction generalizing x with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hΦ]
  | mul a b iha ihb => rw [map_mul, map_mul, mul_smul, mul_smul, iha, ihb]
  | add a b iha ihb => rw [map_add, map_add, add_smul, add_smul, map_add, iha, ihb]

theorem ev_apply_eigenvector {S : Type*} [CommRing S] {X : Type*} [AddCommGroup X] [Module S X]
    (t : ι → Module.End S X) (χ : ι → S) (x : X) (hx : ∀ i, t i x = χ i • x)
    (w : FreeAlgebra ℤ ι) : ev t w x = ev χ w • x := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hx]
  | mul a b iha ihb =>
    rw [map_mul, map_mul, Module.End.mul_apply, ihb, map_smul, iha, smul_smul, mul_comm]
  | add a b iha ihb => rw [map_add, map_add, LinearMap.add_apply, iha, ihb, add_smul]

theorem ev_mem_adjoin {S : Type*} [CommRing S] {A : Type*} [Ring A] [Algebra S A] (t : ι → A)
    (w : FreeAlgebra ℤ ι) : ev t w ∈ Algebra.adjoin S (Set.range t) := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap]; exact Subalgebra.intCast_mem _ r
  | grade1 i => rw [FreeAlgebra.lift_ι_apply]; exact Algebra.subset_adjoin ⟨i, rfl⟩
  | mul a b iha ihb => rw [map_mul]; exact Subalgebra.mul_mem _ iha ihb
  | add a b iha ihb => rw [map_add]; exact Subalgebra.add_mem _ iha ihb

end Words

section Coeff

theorem map_binarySubst {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (binarySubst R M P) = binarySubst R' M (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R) =
      (binarySubst R' M : MvPolynomial (Fin 2) R' →+* MvPolynomial (Fin 2) R').comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_C, MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_X, MvPolynomial.map_X, map_sum,
        map_mul, map_intCast]
  exact congrFun (congrArg DFunLike.coe h) P

variable (N n : ℕ)

structure IsCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (Φ : H1 R N n →+ H1 R' N n) : Prop where
  mk_spec : ∀ z : ↥(coeffCocycles (ρSym R N n)), ∃ w : ↥(coeffCocycles (ρSym R' N n)),
    (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R') =
      MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
    Φ (coeffH1Mk _ z) = coeffH1Mk _ w
  smul : ∀ (c : R) (x : H1 R N n), Φ (c • x) = φ c • Φ x
  hecke : ∀ (ℓ : ℕ) [NeZero ℓ] (x : H1 R N n), Φ (TH R N n ℓ x) = TH R' N n ℓ (Φ x)
  inj : ∀ r : R' →+ R, (∀ a : R, r (φ a) = a) → Function.Injective Φ

theorem exists_isCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ∃ Φ : H1 R N n →+ H1 R' N n, IsCoeffMap N n φ Φ := by
  obtain ⟨Φ, h1, h2, h3, -, h5⟩ := exists_coeffH1_map_ringHom_binaryFormRepSL φ n N
  exact ⟨Φ, ⟨h1, h2, fun ℓ _ x => h3 ℓ (TH R N n ℓ) (TH R' N n ℓ) (isCoeffHeckeOnH1_TH R N n ℓ)
    (isCoeffHeckeOnH1_TH R' N n ℓ) x, h5⟩⟩

variable {N n}

theorem IsCoeffMap.comp_apply {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
    {φ : R →+* R'} {ψ : R' →+* R''} {Φ : H1 R N n →+ H1 R' N n} {Ψ : H1 R' N n →+ H1 R'' N n}
    {Θ : H1 R N n →+ H1 R'' N n} (hΦ : IsCoeffMap N n φ Φ) (hΨ : IsCoeffMap N n ψ Ψ)
    (hΘ : IsCoeffMap N n (ψ.comp φ) Θ) (x : H1 R N n) : Θ x = Ψ (Φ x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨w, hw, hΦz⟩ := hΦ.mk_spec z
  obtain ⟨w', hw', hΨw⟩ := hΨ.mk_spec w
  obtain ⟨w'', hw'', hΘz⟩ := hΘ.mk_spec z
  rw [hΘz, hΦz, hΨw]
  congr 1
  refine Subtype.ext (funext fun g => Subtype.ext ?_)
  rw [hw'', hw', hw, MvPolynomial.map_map]

theorem exists_int_form (v : ↥(BinaryForm ℚ n)) :
    ∃ (d : ℤ) (v₀ : ↥(BinaryForm ℤ n)), d ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) (v₀ : MvPolynomial (Fin 2) ℤ) =
        (d : ℚ) • (v : MvPolynomial (Fin 2) ℚ) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    ((v : MvPolynomial (Fin 2) ℚ).support.image fun m => (v : MvPolynomial (Fin 2) ℚ).coeff m)
  have hb0 : ((b : ℤ)) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  choose! c hc using hb
  refine ⟨b, ⟨∑ m ∈ (v : MvPolynomial (Fin 2) ℚ).support,
      MvPolynomial.monomial m (c ((v : MvPolynomial (Fin 2) ℚ).coeff m)), ?_⟩, hb0, ?_⟩
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
    have hv := (MvPolynomial.mem_homogeneousSubmodule n _).mp v.2
    have hdeg := hv (MvPolynomial.mem_support_iff.mp hm)
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]; exact hdeg
  · simp only [map_sum, MvPolynomial.map_monomial]
    conv_rhs => rw [(v : MvPolynomial (Fin 2) ℚ).as_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h := hc _ (Finset.mem_image_of_mem _ hm)
    rw [MvPolynomial.smul_monomial, eq_intCast]
    rw [eq_intCast] at h
    rw [h, zsmul_eq_mul, smul_eq_mul]

theorem IsCoeffMap.exists_smul_eq_zero_of_rat {Φ : H1 ℤ N n →+ H1 ℚ N n}
    (hΦ : IsCoeffMap N n (Int.castRingHom ℚ) Φ) (x : H1 ℤ N n) (hx : Φ x = 0) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x = 0 := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨w, hw, hΦz⟩ := hΦ.mk_spec z
  rw [hΦz, coeffH1Mk_eq_zero_iff, mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx
  obtain ⟨d, v₀, hd, hv₀⟩ := exists_int_form v
  refine ⟨d, hd, ?_⟩
  rw [← map_zsmul, coeffH1Mk_eq_zero_iff, mem_coeffCoboundaries_iff]
  refine ⟨v₀, funext fun g => Subtype.ext ?_⟩
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hvg := congrArg (fun f : Gamma0 N → ↥(BinaryForm ℚ n) => ((f g : ↥(BinaryForm ℚ n)) :
    MvPolynomial (Fin 2) ℚ)) hv
  rw [hw g] at hvg
  simp only [Submodule.coe_sub, map_sub, SetLike.val_smul, Pi.smul_apply, map_zsmul]
  change MvPolynomial.map (Int.castRingHom ℚ) (binarySubst ℤ _ (v₀ : MvPolynomial (Fin 2) ℤ)) - _ = _
  rw [map_binarySubst, hv₀, ← hvg, map_smul, ← smul_sub, ← Int.cast_smul_eq_zsmul ℚ]
  rfl

theorem eq_zero_of_prime_smul_eq_zero {p : ℕ} (hp : p.Prime) (hnp : n < p) (hpN : ¬ p ∣ N)
    (x : H1 ℤ N n) (hx : (p : ℤ) • x = 0) : x = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  rw [← map_zsmul, coeffH1Mk_eq_zero_iff] at hx
  rw [coeffH1Mk_eq_zero_iff]
  refine mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt (R := ℤ) (K := ZMod p) p
    (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) (p : ℤ)
    (fun r => ?_) (fun a b h => ?_) n N hnp hpN z ?_
  · exact ZMod.intCast_zmod_eq_zero_iff_dvd r p
  · exact mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0) h
  · simpa only [SetLike.val_smul] using hx

theorem eq_zero_of_prime_pow_smul_eq_zero {p : ℕ} (hp : p.Prime) (hnp : n < p) (hpN : ¬ p ∣ N)
    (e : ℕ) (x : H1 ℤ N n) (hx : ((p : ℤ) ^ e) • x = 0) : x = 0 := by
  induction e generalizing x with
  | zero => simpa using hx
  | succ e ih =>
    apply ih
    apply eq_zero_of_prime_smul_eq_zero hp hnp hpN
    rwa [smul_smul, ← pow_succ']

theorem eq_zero_of_torsion {F : Type} [Field F] {p : ℕ} [CharP F p] (hp : p.Prime)
    (hnp : n < p) (hpN : ¬ p ∣ N) (Φ : H1 ℤ N n →+ H1 F N n)
    (x : H1 ℤ N n) (d : ℤ) (hd : d ≠ 0) (hx : d • x = 0) : Φ x = 0 := by

  have hx' : (d.natAbs : ℤ) • x = 0 := by
    rcases Int.natAbs_eq d with h | h
    · rw [← h, hx]
    · rw [h] at hx; rwa [neg_smul, neg_eq_zero] at hx
  have hD : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  obtain ⟨e, d', hd', hD'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD p hp.ne_one
  rw [hD', Nat.cast_mul, Nat.cast_pow, ← smul_smul] at hx'
  have h1 : (d' : ℤ) • x = 0 := eq_zero_of_prime_pow_smul_eq_zero hp hnp hpN e _ hx'
  have h2 : ((d' : ℤ) : F) • Φ x = 0 := by
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul, h1, map_zero]
  rw [Int.cast_natCast] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd ((CharP.cast_eq_zero_iff F p d').mp h) hd'
  · exact h

theorem IsCoeffMap.injective_ratComplex {Φ : H1 ℚ N n →+ H1 ℂ N n}
    (hΦ : IsCoeffMap N n (algebraMap ℚ ℂ) Φ) : Function.Injective Φ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  refine hΦ.inj g.toAddMonoidHom fun a => ?_
  exact congrFun (congrArg DFunLike.coe hg) a

theorem IsCoeffMap.span_range_eq_top [NeZero N] {F : Type} [Field F] [CharP F 3]
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) {Φ : H1 ℤ N n →+ H1 F N n}
    (hΦ : IsCoeffMap N n (Int.castRingHom F) Φ) :
    Submodule.span F (Set.range Φ) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨m, c, y, w, hw, hz⟩ :=
    exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two F n N hε z
  choose w' hw' hΦy using fun i => hΦ.mk_spec (y i)
  have hzw : (z : Gamma0 N → ↥(BinaryForm F n)) - ((∑ i, c i • w' i :
      ↥(coeffCocycles (ρSym F N n))) : Gamma0 N → ↥(BinaryForm F n)) = w := by
    funext g
    apply Subtype.ext
    simp only [Pi.sub_apply, Submodule.coe_sub, hz, Submodule.coe_sum, Finset.sum_apply,
      SetLike.val_smul, Pi.smul_apply, hw']
    abel
  have hcl : coeffH1Mk (ρSym F N n) z = coeffH1Mk _ (∑ i, c i • w' i) := by
    rw [coeffH1Mk_eq_iff, hzw]; exact hw
  rw [hcl, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, ← hΦy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Coeff

section Lattice

variable (N : ℕ) (k : ℤ)

abbrev MF : Type := ModularForm (Gamma0 N) k

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

noncomputable def qCoeffLin (m : ℕ) : MF N k →ₗ[ℂ] ℂ where
  toFun f := qCoeff f m
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 ⇑(f + g)).coeff m = _
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
    rfl
  map_smul' c f := by
    change (UpperHalfPlane.qExpansion 1 ⇑(c • f)).coeff m = _
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f,
      map_smul]
    rfl

@[scoped simp] theorem qCoeffLin_apply (m : ℕ) (f : MF N k) : qCoeffLin N k m f = qCoeff f m := rfl

theorem eq_zero_of_forall_qCoeff (f : MF N k) (h : ∀ m, qCoeff f m = 0) : f = 0 :=
  ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods N) fun m => by
    rw [h m, ← qCoeffLin_apply N k m (0 : MF N k), map_zero]

noncomputable def intFormsAdd : AddSubgroup (MF N k) where
  carrier := {f | ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ)}
  zero_mem' m := ⟨0, by rw [Int.cast_zero, ← qCoeffLin_apply, map_zero]⟩
  add_mem' {f g} hf hg m := by
    obtain ⟨a, ha⟩ := hf m
    obtain ⟨b, hb⟩ := hg m
    exact ⟨a + b, by rw [← qCoeffLin_apply, map_add, qCoeffLin_apply, qCoeffLin_apply, ha, hb,
      Int.cast_add]⟩
  neg_mem' {f} hf m := by
    obtain ⟨a, ha⟩ := hf m
    exact ⟨-a, by rw [← qCoeffLin_apply, map_neg, qCoeffLin_apply, ha, Int.cast_neg]⟩

noncomputable def intForms : Submodule ℤ (MF N k) := (intFormsAdd N k).toIntSubmodule

theorem mem_intForms (f : MF N k) : f ∈ intForms N k ↔ ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ) :=
  Iff.rfl

variable {N k}

noncomputable def zc (f : ↥(intForms N k)) (m : ℕ) : ℤ := (f.2 m).choose

theorem zc_spec (f : ↥(intForms N k)) (m : ℕ) : (zc f m : ℂ) = qCoeff (f : MF N k) m :=
  ((f.2 m).choose_spec).symm

theorem zc_add (f g : ↥(intForms N k)) (m : ℕ) : zc (f + g) m = zc f m + zc g m := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_add, zc_spec, zc_spec, zc_spec, Submodule.coe_add, ← qCoeffLin_apply, map_add]
  rfl

variable (N k)

noncomputable def zcHom : ↥(intForms N k) →+ (ℕ → ℤ) where
  toFun := zc
  map_zero' := funext fun m => Int.cast_injective (α := ℂ) (by
    rw [zc_spec, Submodule.coe_zero, Pi.zero_apply, Int.cast_zero, ← qCoeffLin_apply, map_zero])
  map_add' f g := funext fun m => zc_add f g m

theorem zcHom_apply (f : ↥(intForms N k)) (m : ℕ) : zcHom N k f m = zc f m := rfl

theorem zcHom_injective : Function.Injective (zcHom N k) := by
  intro f g h
  apply Subtype.ext
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_qCoeff N k _ fun m => ?_
  have hm := congrFun h m
  rw [zcHom_apply, zcHom_apply] at hm
  change qCoeff (⇑((f : MF N k) - (g : MF N k))) m = 0
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply, ← zc_spec, ← zc_spec, hm, sub_self]

theorem zc_zsmul (d : ℤ) (f : ↥(intForms N k)) (m : ℕ) : zc (d • f) m = d * zc f m := by
  have h := congrFun (map_zsmul (zcHom N k) d f) m
  rwa [zcHom_apply, Pi.smul_apply, zcHom_apply, smul_eq_mul] at h

theorem exists_finset_ker_eq_bot [NeZero N] :
    ∃ s : Finset ℕ, ∀ f : MF N k, (∀ m ∈ s, qCoeff f m = 0) → f = 0 := by
  haveI : FiniteDimensional ℂ (MF N k) := ModularForm.finiteDimensional_Gamma0 N k
  let K : Finset ℕ → Submodule ℂ (MF N k) := fun s => ⨅ m ∈ s, LinearMap.ker (qCoeffLin N k m)
  obtain ⟨W, ⟨s₀, rfl⟩, hmin⟩ := WellFounded.has_min (IsWellFounded.wf (r := (· < ·)))
    (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨s₀, fun f hf => ?_⟩
  have hfK : f ∈ K s₀ := by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply]
    exact hf
  have hle : ∀ m, K s₀ ≤ LinearMap.ker (qCoeffLin N k m) := by
    intro m
    by_contra hnot
    have hlt : K (insert m s₀) < K s₀ := by
      refine lt_of_le_of_ne ?_ ?_
      · exact biInf_mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
      · intro heq
        apply hnot
        rw [← heq]
        exact biInf_le _ (Finset.mem_insert_self m s₀)
    exact hmin _ ⟨_, rfl⟩ hlt
  refine eq_zero_of_forall_qCoeff N k f fun m => ?_
  have := hle m hfK
  rwa [LinearMap.mem_ker, qCoeffLin_apply] at this

theorem exists_basis_intForms [NeZero N] :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ ↥(intForms N k)) := by
  obtain ⟨s, hs⟩ := exists_finset_ker_eq_bot N k

  let ev : ↥(intForms N k) →ₗ[ℤ] (↥s → ℤ) :=
    { toFun := fun f i => zc f i
      map_add' := fun f g => funext fun i => zc_add f g i
      map_smul' := fun d f => funext fun i => by
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, zc_zsmul] }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    refine hs _ fun m hm => ?_
    rw [← zc_spec, show zc f m = 0 from congrFun hf ⟨m, hm⟩, Int.cast_zero]
  obtain ⟨r, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ↥s) (LinearMap.range ev)
  exact ⟨r, ⟨b.map (LinearEquiv.ofInjective ev hev).symm⟩⟩

def zcHecke (k : ℤ) (ℓ : ℕ) (a : ℕ → ℤ) (m : ℕ) : ℤ :=
  a (m * ℓ) + if ℓ ∣ m then (ℓ : ℤ) ^ (k - 1).toNat * a (m / ℓ) else 0

theorem cast_zcHecke {S : Type*} [DivisionRing S] [CharZero S] {k : ℤ} (hk : 1 ≤ k) (ℓ : ℕ) (a : ℕ → ℤ) (m : ℕ) :
    (zcHecke k ℓ a m : S) = (a (m * ℓ) : S) + if ℓ ∣ m then (ℓ : S) ^ (k - 1) * (a (m / ℓ) : S) else 0 := by
  have hk' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  unfold zcHecke
  split_ifs with h
  · push_cast
    rw [← zpow_natCast, hk']
  · push_cast; rfl

variable {N k} in
theorem qCoeff_heckeTLin (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) (m : ℕ) :
    qCoeff (ModularForm.heckeTLin k hℓ hℓN (f : MF N k)) m = (zcHecke k ℓ (zc f) m : ℂ) := by
  rw [ModularForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT (f : MF N k)
    (one_mem_strictPeriods N) hℓ.ne_zero m, ModularForm.coeffHeckeT_apply, cast_zcHecke hk]
  simp only [← zc_spec]

theorem heckeTLin_mem_intForms (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : ↥(intForms N k)) : ModularForm.heckeTLin k hℓ hℓN (f : MF N k) ∈ intForms N k :=
  fun m => ⟨zcHecke k ℓ (zc f) m, qCoeff_heckeTLin hk hℓ hℓN f m⟩

noncomputable def TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    ↥(intForms N k) →ₗ[ℤ] ↥(intForms N k) :=
  ((ModularForm.heckeTLin k hℓ hℓN).toAddMonoidHom.toIntLinearMap).restrict
    fun f hf => heckeTLin_mem_intForms N k hk hℓ hℓN ⟨f, hf⟩

@[scoped simp] theorem coe_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) :
    ((TL N k hk hℓ hℓN f : ↥(intForms N k)) : MF N k) = ModularForm.heckeTLin k hℓ hℓN (f : MF N k) := rfl

theorem zc_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) (m : ℕ) :
    zc (TL N k hk hℓ hℓN f) m = zcHecke k ℓ (zc f) m := by
  apply Int.cast_injective (α := ℂ)
  rw [zc_spec, coe_TL, qCoeff_heckeTLin hk hℓ hℓN f m]

theorem TL_comm (hk : 1 ≤ k) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ' : ℓ'.Prime)
    (hℓ'N : ¬ ℓ' ∣ N) : Commute (TL N k hk hℓ hℓN) (TL N k hk hℓ' hℓ'N) := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  change ModularForm.heckeTLin k hℓ hℓN (ModularForm.heckeTLin k hℓ' hℓ'N (f : MF N k)) =
    ModularForm.heckeTLin k hℓ' hℓ'N (ModularForm.heckeTLin k hℓ hℓN (f : MF N k))
  exact congrFun (congrArg DFunLike.coe (ModularForm.heckeTLin_comm k hℓ hℓN hℓ' hℓ'N).eq) (f : MF N k)

variable (F : Type) [Field F]

noncomputable def redL : ↥(intForms N k) →ₗ[ℤ] PowerSeries F :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => PowerSeries.mk fun m => ((zc f m : ℤ) : F)
      map_zero' := by
        ext m
        rw [PowerSeries.coeff_mk, map_zero, show zc 0 m = 0 from congrFun (map_zero (zcHom N k)) m,
          Int.cast_zero]
      map_add' := fun f g => by
        ext m
        simp only [PowerSeries.coeff_mk, map_add, zc_add, Int.cast_add] }

@[scoped simp] theorem coeff_redL (f : ↥(intForms N k)) (m : ℕ) :
    PowerSeries.coeff m (redL N k F f) = ((zc f m : ℤ) : F) := by
  simp [redL, PowerSeries.coeff_mk]

noncomputable def red : F ⊗[ℤ] ↥(intForms N k) →ₗ[F] PowerSeries F :=
  (redL N k F).liftBaseChange F

@[scoped simp] theorem red_tmul (c : F) (f : ↥(intForms N k)) : red N k F (c ⊗ₜ f) = c • redL N k F f :=
  LinearMap.liftBaseChange_tmul F _ c f

theorem red_mem_modPMod (y : F ⊗[ℤ] ↥(intForms N k)) : red N k F y ∈ ModPForms.modPMod N k F := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c f =>
    rw [red_tmul]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(f : MF N k), zc f, fun m => (zc_spec f m).symm, ?_⟩)
    rfl
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem heckePS_add (ℓ : ℕ) (φ ψ : PowerSeries F) :
    ModPForms.heckePS k ℓ (φ + ψ) = ModPForms.heckePS k ℓ φ + ModPForms.heckePS k ℓ ψ := by
  ext m
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_add]
  split_ifs <;> ring

theorem heckePS_smul (ℓ : ℕ) (c : F) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (c • φ) = c • ModPForms.heckePS k ℓ φ := by
  ext m
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_smul, smul_eq_mul]
  split_ifs <;> ring

theorem red_baseChange_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (y : F ⊗[ℤ] ↥(intForms N k)) :
    red N k F ((TL N k hk hℓ hℓN).baseChange F y) = ModPForms.heckePS k ℓ (red N k F y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; ext m; simp [ModPForms.heckePS, PowerSeries.coeff_mk]
  | tmul c f =>
    rw [LinearMap.baseChange_tmul, red_tmul, red_tmul, heckePS_smul]
    congr 1
    ext m
    rw [coeff_redL, zc_TL]
    simp only [ModPForms.heckePS, PowerSeries.coeff_mk, coeff_redL, zcHecke]
    have hk' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    split_ifs with h
    · push_cast; rw [← zpow_natCast, hk']
    · push_cast; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, heckePS_add]

variable {F}

theorem exists_smul_eq_of_forall_dvd {p : ℕ} (hp : p ≠ 0) (g : ↥(intForms N k))
    (hg : ∀ m, (p : ℤ) ∣ zc g m) : ∃ g' : ↥(intForms N k), (p : ℤ) • g' = g := by
  choose q hq using hg
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  refine ⟨⟨(p : ℂ)⁻¹ • (g : MF N k), fun m => ⟨q m, ?_⟩⟩, Subtype.ext ?_⟩
  · rw [← qCoeffLin_apply, map_smul, qCoeffLin_apply, ← zc_spec, hq m, smul_eq_mul]
    push_cast
    field_simp
  · rw [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, Int.cast_natCast,
      mul_inv_cancel₀ hp', one_smul]

theorem dvd_of_sum_smul_redL_eq_zero {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ ↥(intForms N k)) (d : Fin r → ℤ)
    (hd : ∑ i, ((d i : ℤ) : F) • redL N k F (b i) = 0) (i : Fin r) : (p : ℤ) ∣ d i := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set g : ↥(intForms N k) := ∑ i, d i • b i with hg
  have hredg : redL N k F g = 0 := by
    rw [hg, map_sum]
    simp only [map_zsmul]
    simpa only [Int.cast_smul_eq_zsmul] using hd
  have hdvd : ∀ m, (p : ℤ) ∣ zc g m := fun m => by
    have := congrArg (PowerSeries.coeff m) hredg
    rw [coeff_redL, map_zero] at this
    exact (CharP.intCast_eq_zero_iff F p _).mp this
  obtain ⟨g', hg'⟩ := exists_smul_eq_of_forall_dvd N k hp g hdvd
  have hrepr : b.equivFun g = d := by
    rw [hg, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  have := congrFun hrepr i
  rw [← hg', map_zsmul, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨_, this.symm⟩

theorem linearIndependent_redL {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ ↥(intForms N k)) :
    LinearIndependent F (fun i => redL N k F (b i)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let e := Module.Free.chooseBasis (ZMod p) F
  rw [Fintype.linearIndependent_iff]
  intro c hc i

  refine e.ext_elem fun j => ?_
  rw [map_zero, Finsupp.zero_apply]

  let d : Fin r → ℤ := fun i' => ((e.repr (c i') j).val : ℤ)
  have hdcast : ∀ i', ((d i' : ℤ) : ZMod p) = e.repr (c i') j := fun i' => by
    simp only [d, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hrel : ∑ i', ((d i' : ℤ) : F) • redL N k F (b i') = 0 := by
    ext m
    have hm := congrArg (PowerSeries.coeff m) hc
    simp only [map_sum, map_smul, coeff_redL, smul_eq_mul, map_zero] at hm ⊢

    have hm' : ∑ i', ((zc (b i') m : ℤ) : ZMod p) • c i' = 0 := by
      rw [← hm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Algebra.smul_def, map_intCast, mul_comm]
    have hj := congrArg (fun x : F => e.repr x j) hm'
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply] at hj
    have : (∑ i', ((d i' : ℤ) : F) * ((zc (b i') m : ℤ) : F)) =
        algebraMap (ZMod p) F (∑ i', ((zc (b i') m : ℤ) : ZMod p) * e.repr (c i') j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, map_intCast, ← hdcast, map_intCast, mul_comm]
    rw [this, hj, map_zero]
  have hdiv := dvd_of_sum_smul_redL_eq_zero N k b d hrel i
  rw [← hdcast, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv]

theorem red_injective [NeZero N] {p : ℕ} [Fact p.Prime] [CharP F p] :
    Function.Injective (red N k F) := by
  obtain ⟨r, ⟨b⟩⟩ := exists_basis_intForms N k
  have hli := linearIndependent_redL N k (F := F) b
  let B := Algebra.TensorProduct.basis F b
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  rw [← B.sum_equivFun y] at hy
  simp only [map_sum, map_smul, B, Algebra.TensorProduct.basis_apply, red_tmul, one_smul] at hy
  have h0 := (Fintype.linearIndependent_iff.mp hli) _ hy
  rw [← B.sum_equivFun y]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]

end Lattice

section Main

variable (N : ℕ) (S₀ : Set ℕ)

def Good (ℓ : ℕ) : Prop := ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀

abbrev GoodPrime : Type := {ℓ : ℕ // Good N S₀ ℓ}

scoped instance neZero_goodPrime (i : GoodPrime N S₀) : NeZero (i : ℕ) := ⟨i.2.1.ne_zero⟩

variable (n : ℕ)

noncomputable def tH (R : Type) [CommRing R] : GoodPrime N S₀ → Module.End R (H1 R N n) :=
  fun i => TH R N n (i : ℕ)

theorem tH_comm (R : Type) [CommRing R] (i j : GoodPrime N S₀) : Commute (tH N S₀ n R i) (tH N S₀ n R j) :=
  TH_comm R N n i.2.1 j.2.1 i.2.2.1 j.2.2.1

abbrev wt : ℤ := (n : ℤ) + 2

theorem one_le_wt : 1 ≤ wt n := by unfold wt; omega

noncomputable def tL : GoodPrime N S₀ → Module.End ℤ ↥(intForms N (wt n)) :=
  fun i => TL N (wt n) (one_le_wt n) i.2.1 i.2.2.1

noncomputable def tM : GoodPrime N S₀ → Module.End ℂ (MF N (wt n)) :=
  fun i => ModularForm.heckeTLin (wt n) i.2.1 i.2.2.1

variable {N S₀ n}

theorem IsCoeffMap.map_ev {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'}
    {Φ : H1 R N n →+ H1 R' N n} (hΦ : IsCoeffMap N n φ Φ) (w : FreeAlgebra ℤ (GoodPrime N S₀))
    (x : H1 R N n) : Φ (ev (tH N S₀ n R) w x) = ev (tH N S₀ n R') w (Φ x) :=
  map_ev_apply (tH N S₀ n R) (tH N S₀ n R') Φ (fun i y => hΦ.hecke i y) w x

theorem ev_lam_eq_zero [NeZero N] {p : ℕ} (hp : p.Prime) (hp3 : p = 3)
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (hpN : ¬ p ∣ N)
    {F : Type} [Field F] [CharP F p] (hnp : n < p) (lam : ℕ → F)
    (xF : H1 F N n) (hxF0 : xF ≠ 0) (heig : ∀ i : GoodPrime N S₀, tH N S₀ n F i xF = lam i • xF)
    (w : FreeAlgebra ℤ (GoodPrime N S₀)) (hw : ev (tL N S₀ n) w = 0) :
    ev (fun i : GoodPrime N S₀ => lam i) w = 0 := by
  subst hp3

  have hM : ∀ f : MF N (wt n), ev (tM N S₀ n) w f = 0 := by
    have hL : ∀ f : ↥(intForms N (wt n)), ev (tM N S₀ n) w (f : MF N (wt n)) = 0 := fun f => by
      have h := map_ev_apply (tL N S₀ n) (tM N S₀ n) (intForms N (wt n)).subtype.toAddMonoidHom
        (fun i x => rfl) w f
      rw [hw] at h
      simpa using h.symm
    have hspan := ModularForm.span_setOf_qCoeff_intCast_eq_top N (wt n)
    intro f
    have hf : f ∈ Submodule.span ℂ {f : MF N (wt n) | ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ)} := by
      rw [hspan]; exact Submodule.mem_top
    have hle : Submodule.span ℂ {f : MF N (wt n) | ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ)} ≤
        LinearMap.ker (ev (tM N S₀ n) w) :=
      Submodule.span_le.mpr fun g hg => hL ⟨g, hg⟩
    exact hle hf

  have hnil : IsNilpotent (ev (tH N S₀ n ℂ) w) := by
    haveI := finiteDimensional_coeffH1 N (ρSym ℂ N n)
    refine Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero (tH N S₀ n ℂ)
      (tH_comm N S₀ n ℂ) _ (ev_mem_adjoin _ w) fun χ v hv0 hv => ?_
    classical
    let Λ : ℕ → ℂ := fun ℓ => if h : Good N S₀ ℓ then χ ⟨ℓ, h⟩ else 0
    have hoccC : IsEigensystemH1 N (ρSym ℂ N n) (fun ℓ => binaryFormAlphaAdj ℂ n ℓ) S₀ Λ := by
      refine ⟨v, hv0, fun ℓ hℓ hℓN hℓS => ?_⟩
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      refine ⟨TH ℂ N n ℓ, isCoeffHeckeOnH1_TH ℂ N n ℓ, ?_⟩
      have := hv ⟨ℓ, hℓ, hℓN, hℓS⟩
      simp only [Λ, dif_pos (show Good N S₀ ℓ from ⟨hℓ, hℓN, hℓS⟩)]
      exact this
    obtain ⟨f, hf0, hf⟩ := exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1 N n S₀ Λ hoccC
    have hfeig : ∀ i : GoodPrime N S₀, tM N S₀ n i f = χ i • f := fun i => by
      have := hf i i.2.1 i.2.2.1 i.2.2.2
      simp only [Λ, dif_pos i.2] at this
      exact this
    have h1 := ev_apply_eigenvector (tM N S₀ n) χ f hfeig w
    rw [hM f] at h1
    have hχ : ev χ w = 0 := (smul_eq_zero.mp h1.symm).resolve_right hf0
    rw [ev_apply_eigenvector (tH N S₀ n ℂ) χ v hv w, hχ, zero_smul]
  obtain ⟨m, hm⟩ := hnil

  obtain ⟨ΦF, hΦF⟩ := exists_isCoeffMap N n (Int.castRingHom F)
  obtain ⟨Φq, hΦq⟩ := exists_isCoeffMap N n (Int.castRingHom ℚ)
  obtain ⟨Φqc, hΦqc⟩ := exists_isCoeffMap N n (algebraMap ℚ ℂ)
  obtain ⟨Φc, hΦc⟩ := exists_isCoeffMap N n ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ))

  have hZ : ∀ x : H1 ℤ N n, ΦF (ev (tH N S₀ n ℤ) (w ^ m) x) = 0 := by
    intro x
    have hc : Φc (ev (tH N S₀ n ℤ) (w ^ m) x) = 0 := by
      rw [hΦc.map_ev, map_pow, hm, LinearMap.zero_apply]
    have hq : Φq (ev (tH N S₀ n ℤ) (w ^ m) x) = 0 := by
      apply hΦqc.injective_ratComplex
      rw [map_zero, ← hΦq.comp_apply hΦqc hΦc, hc]
    obtain ⟨d, hd, hdx⟩ := hΦq.exists_smul_eq_zero_of_rat _ hq
    exact eq_zero_of_torsion hp hnp hpN ΦF _ d hd hdx

  have hF : ev (tH N S₀ n F) (w ^ m) = 0 := by
    have hspan := hΦF.span_range_eq_top hε
    refine LinearMap.ext fun y => ?_
    have hy : y ∈ Submodule.span F (Set.range ΦF) := by rw [hspan]; exact Submodule.mem_top
    rw [LinearMap.zero_apply]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      rw [← hΦF.map_ev, hZ x]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]

  have h5 := ev_apply_eigenvector (tH N S₀ n F) (fun i => lam i) xF heig (w ^ m)
  rw [hF, LinearMap.zero_apply, map_pow] at h5
  exact IsNilpotent.eq_zero ⟨m, ((smul_eq_zero.mp h5.symm).resolve_right hxF0)⟩

theorem tL_comm (i j : GoodPrime N S₀) : Commute (tL N S₀ n i) (tL N S₀ n j) :=
  TL_comm N (wt n) (one_le_wt n) i.2.1 i.2.2.1 j.2.1 j.2.2.1

theorem exists_algHom_adjoin {F : Type} [Field F] (lam : ℕ → F)
    (hker : ∀ w : FreeAlgebra ℤ (GoodPrime N S₀), ev (tL N S₀ n) w = 0 →
      ev (fun i : GoodPrime N S₀ => lam i) w = 0) :
    ∃ χ : ↥(Algebra.adjoin ℤ (Set.range (tL N S₀ n))) →ₐ[ℤ] F,
      ∀ i : GoodPrime N S₀, χ ⟨tL N S₀ n i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = lam i := by
  set A := Algebra.adjoin ℤ (Set.range (tL N S₀ n)) with hAdef
  have hA : A = (ev (tL N S₀ n)).range :=
    Algebra.adjoin_range_eq_range_freeAlgebra_lift ℤ (X := GoodPrime N S₀) (tL N S₀ n)
  let f : FreeAlgebra ℤ (GoodPrime N S₀) →ₐ[ℤ] ↥(ev (tL N S₀ n)).range := (ev (tL N S₀ n)).rangeRestrict
  have hf : Function.Surjective f := AlgHom.rangeRestrict_surjective _
  have hkerle : RingHom.ker (f : FreeAlgebra ℤ (GoodPrime N S₀) →+* ↥(ev (tL N S₀ n)).range) ≤
      RingHom.ker (ev (fun i : GoodPrime N S₀ => lam i) : FreeAlgebra ℤ (GoodPrime N S₀) →+* F) := by
    intro w hw
    rw [RingHom.mem_ker] at hw ⊢
    exact hker w (congrArg Subtype.val hw)
  let χ₀ : ↥(ev (tL N S₀ n)).range →+* F :=
    RingHom.liftOfRightInverse (f : FreeAlgebra ℤ (GoodPrime N S₀) →+* _) (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨_, hkerle⟩
  have hχ₀ : ∀ w, χ₀ (f w) = ev (fun i : GoodPrime N S₀ => lam i) w := fun w =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkerle⟩ w
  let e : ↥A ≃ₐ[ℤ] ↥(ev (tL N S₀ n)).range := Subalgebra.equivOfEq _ _ hA
  refine ⟨{ toRingHom := χ₀.comp (e : ↥A →+* ↥(ev (tL N S₀ n)).range), commutes' := fun r => ?_ }, fun i => ?_⟩
  · simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
      eq_intCast, map_intCast]
  · change χ₀ (e ⟨tL N S₀ n i, _⟩) = lam i
    have he : e ⟨tL N S₀ n i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = f (FreeAlgebra.ι ℤ i) := by
      apply Subtype.ext
      change tL N S₀ n i = ev (tL N S₀ n) (FreeAlgebra.ι ℤ i)
      rw [FreeAlgebra.lift_ι_apply]
    rw [he, hχ₀, FreeAlgebra.lift_ι_apply]

end Main

end C3ES
p2m_reactivate "P2MW.S_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two.C3ES"

open C3ES in

theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : 3 ∈ S₀) (F : Type) [Field F] [CharP F 3]
    (a : ℕ) (ha : a ≤ 2) (lam : ℕ → F)
    (hocc : HeckeEis.IsEigensystemH1 N'
      ((HeckeEis.binaryFormRepSL F a).comp (CongruenceSubgroup.Gamma0 N').subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F a ℓ) S₀ lam) :
    ∃ (j : ℕ) (ψ : PowerSeries F) (mu : ℕ → F),
      ψ ∈ ModPForms.modPMod N' ((a : ℤ) + 2) F ∧ ModPForms.IsModPEigen N' S₀ ((a : ℤ) + 2) ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : F) ^ j * lam ℓ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnp : a < 3 := by omega
  obtain ⟨xF, hxF0, hxF⟩ := hocc
  have heig : ∀ i : GoodPrime N' S₀, tH N' S₀ a F i xF = lam i • xF := fun i => by
    obtain ⟨T, hT, hTx⟩ := hxF i i.2.1 i.2.2.1 i.2.2.2
    have hT' : T = TH F N' a (i : ℕ) := eq_TH F N' a hT
    rw [hT'] at hTx
    exact hTx
  have hker := fun w hw => ev_lam_eq_zero Nat.prime_three rfl hε hpN' hnp lam xF hxF0 heig w hw
  obtain ⟨χ, hχ⟩ := exists_algHom_adjoin (N := N') (S₀ := S₀) (n := a) lam hker
  obtain ⟨r, ⟨b⟩⟩ := exists_basis_intForms N' (wt a)
  haveI : Module.Finite ℤ ↥(intForms N' (wt a)) := Module.Finite.of_basis b
  obtain ⟨y, hy0, hy⟩ :=
    Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom (tL N' S₀ a) tL_comm χ
  refine ⟨0, red N' (wt a) F y, lam, red_mem_modPMod N' (wt a) F y, ⟨fun h => hy0 ?_, ?_⟩,
    fun ℓ _ _ _ => by rw [pow_zero, one_mul]⟩
  · exact red_injective N' (wt a) (F := F) (by rw [h, map_zero])
  · intro ℓ hℓ hℓN hℓS
    have h1 := hy ⟨ℓ, hℓ, hℓN, hℓS⟩
    rw [hχ] at h1
    have h2 := congrArg (red N' (wt a) F) h1
    rw [map_smul] at h2
    rw [← h2]
    exact (red_baseChange_TL N' (wt a) F (one_le_wt a) hℓ hℓN y).symm

end S_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two (solution)
