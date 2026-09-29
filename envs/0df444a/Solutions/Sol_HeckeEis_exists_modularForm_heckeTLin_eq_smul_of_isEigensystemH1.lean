-- Prove2me | solution 1 for HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/788cced6-c230-5981-a93d-2791f3c02bc5

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL
import Theorems.Thm_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
import Theorems.Thm_CuspForm_exists_qCoeff_conj
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1
p2m_attr_erase "instance" "FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"

set_option autoImplicit false

namespace C3ESW1

open CongruenceSubgroup HeckeEis ModularFormClass
open scoped MatrixGroups

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

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

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

noncomputable def heckeZ1par {ρ : Representation K (Gamma0 N) V} {a : V →ₗ[K] V} (ha : IsCompat N ℓ ρ a) :
    ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffParabolicCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffParabolicCocycles N ℓ ρ a ha hz

noncomputable def heckeH1par (ha : IsCompat N ℓ ρ a) : coeffH1par ρ →ₗ[K] coeffH1par ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype) (heckeZ1par ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1par_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffParabolicCocycles ρ)) :
    heckeH1par ha (coeffH1parMk ρ z) = coeffH1parMk ρ (heckeZ1par ha z) := rfl

theorem heckeH1par_prop (ha : IsCompat N ℓ ρ a) (z : ↥(coeffParabolicCocycles ρ)) :
    ∃ w : ↥(coeffParabolicCocycles ρ), (w : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z ∧
      heckeH1par ha (coeffH1parMk ρ z) = coeffH1parMk ρ w :=
  ⟨heckeZ1par ha z, rfl, rfl⟩

theorem coeffH1parToH1_heckeH1par (ha : IsCompat N ℓ ρ a) (x : coeffH1par ρ) :
    coeffH1parToH1 ρ (heckeH1par ha x) = heckeH1 ha (coeffH1parToH1 ρ x) := by
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
  rfl

theorem coeffH1parToH1_injective (ρ : Representation K (Gamma0 N) V) :
    Function.Injective (coeffH1parToH1 ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ρ x
  rw [coeffH1parToH1_coeffH1parMk, coeffH1Mk_eq_zero_iff] at hx
  exact (coeffH1parMk_eq_zero_iff ρ z).mpr hx

end Induced

section Cusp

variable (N : ℕ) (k : ℤ)

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

noncomputable def qCoeffLin (m : ℕ) : CuspForm (Gamma0 N) k →ₗ[ℂ] ℂ where
  toFun f := qCoeff f m
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 ⇑(f + g)).coeff m = _
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
    rfl
  map_smul' c f := by
    change (UpperHalfPlane.qExpansion 1 ⇑(c • f)).coeff m = _
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f,
      map_smul]
    rfl

@[scoped simp] theorem qCoeffLin_apply (m : ℕ) (f : CuspForm (Gamma0 N) k) : qCoeffLin N k m f = qCoeff f m := rfl

variable {N k}

theorem eq_of_forall_qCoeff {f g : CuspForm (Gamma0 N) k} (h : ∀ m, qCoeff f m = qCoeff g m) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods N) h

theorem qCoeff_heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) k) (m : ℕ) :
    qCoeff (CuspForm.heckeTLin k hℓ hℓN f) m =
      qCoeff f (m * ℓ) + if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * qCoeff f (m / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods N) hℓ.ne_zero m,
    ModularForm.coeffHeckeT_apply]

theorem heckeTLin_conj {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (g g' : CuspForm (Gamma0 N) k)
    (hg' : ∀ m, qCoeff g' m = starRingEnd ℂ (qCoeff g m)) (c : ℂ)
    (hg : CuspForm.heckeTLin k hℓ hℓN g = c • g) :
    CuspForm.heckeTLin k hℓ hℓN g' = starRingEnd ℂ c • g' := by
  refine eq_of_forall_qCoeff fun m => ?_
  have hgm : qCoeff (CuspForm.heckeTLin k hℓ hℓN g) m = c * qCoeff g m := by
    rw [hg, ← qCoeffLin_apply, map_smul, qCoeffLin_apply, smul_eq_mul]
  rw [qCoeff_heckeTLin] at hgm
  rw [qCoeff_heckeTLin, ← qCoeffLin_apply N k m (starRingEnd ℂ c • g'), map_smul, qCoeffLin_apply,
    smul_eq_mul, hg', hg', hg', ← map_mul, ← hgm, map_add]
  congr 1
  split_ifs with h
  · rw [map_mul, map_zpow₀, Complex.conj_natCast]
  · rw [map_zero]

theorem toModularFormₗ_heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm.toModularFormₗ (CuspForm.heckeTLin k hℓ hℓN f) =
      ModularForm.heckeTLin k hℓ hℓN (CuspForm.toModularFormₗ f) := by
  refine DFunLike.ext _ _ fun τ => ?_
  rw [CuspForm.toModularFormₗ_apply, ModularForm.heckeTLin_apply_apply, CuspForm.heckeTLin_apply_apply]
  congr 1

theorem conclude_of_cuspForm (n : ℕ) (S₀ : Set ℕ) (Λ : ℕ → ℂ) (f : CuspForm (Gamma0 N) ((n : ℤ) + 2))
    (hf0 : f ≠ 0)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ → CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f) :
    ∃ F : ModularForm (Gamma0 N) ((n : ℤ) + 2), F ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN F = Λ ℓ • F := by
  refine ⟨CuspForm.toModularFormₗ f, fun h => hf0 (CuspForm.toModularFormₗ_injective ?_), fun ℓ hℓ hℓN hℓS => ?_⟩
  · rw [h, map_zero]
  · rw [← toModularFormₗ_heckeTLin, hf ℓ hℓ hℓN hℓS, map_smul]

end Cusp

section Main

variable (N : ℕ) [NeZero N] (n : ℕ)

noncomputable abbrev ρC : Representation ℂ (Gamma0 N) ↥(BinaryForm ℂ n) :=
  (binaryFormRepSL ℂ n).comp (Gamma0 N).subtype

theorem isCompat (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρC N n) (binaryFormAlphaAdj ℂ n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ u

theorem main (S₀ : Set ℕ) (Λ : ℕ → ℂ)
    (hocc : IsEigensystemH1 N (ρC N n) (fun ℓ => binaryFormAlphaAdj ℂ n ℓ) S₀ Λ) :
    ∃ f : ModularForm (Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f := by
  obtain ⟨x, hx0, hx⟩ := hocc

  have heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeH1 (isCompat N n ℓ) x = Λ ℓ • x) := by
    intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨T, hT, hTx⟩ := hx ℓ hℓ hℓN hℓS
    rw [unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_heckeH1 (isCompat N n ℓ))] at hTx
    exact hTx
  by_cases hpar : x ∈ LinearMap.range (coeffH1parToH1 (ρC N n))
  ·
    obtain ⟨x', rfl⟩ := hpar
    have hx'0 : x' ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    have heig' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeH1par (isCompat N n ℓ) x' = Λ ℓ • x') := by
      intro ℓ hℓ hℓN hℓS
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      apply coeffH1parToH1_injective
      rw [coeffH1parToH1_heckeH1par, map_smul]
      exact heig ℓ hℓ hℓN hℓS
    obtain ⟨ES, ESbar, hinj, hinjb, hcompl, hH⟩ := exists_eichlerShimura_coeffH1par_binaryFormRepSL N n

    have hx'mem : x' ∈ LinearMap.range ES ⊔ LinearMap.range ESbar := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx'mem
    obtain ⟨f, rfl⟩ := hu
    obtain ⟨g, rfl⟩ := hv

    have hfg : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f ∧
          CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN g = starRingEnd ℂ (Λ ℓ) • g := by
      intro ℓ hℓ hℓN hℓS
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      obtain ⟨hTf, hTg⟩ := hH ℓ hℓ hℓN (heckeH1par (isCompat N n ℓ)) (heckeH1par_prop (isCompat N n ℓ))
      have h1 := heig' ℓ hℓ hℓN hℓS
      rw [← huv, map_add, hTf, hTg, smul_add] at h1

      have h2 : ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f - Λ ℓ • f) =
          -(ESbar (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN g - starRingEnd ℂ (Λ ℓ) • g)) := by
        rw [map_sub, map_sub, map_smul, LinearMap.map_smulₛₗ, starRingEnd_self_apply, neg_sub]
        rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_sub_iff_add_eq, h1, add_comm]
      have hmem : ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f - Λ ℓ • f) ∈
          LinearMap.range ES ⊓ LinearMap.range ESbar := by
        refine ⟨⟨_, rfl⟩, ?_⟩
        rw [h2]
        exact Submodule.neg_mem _ ⟨_, rfl⟩
      rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
      have hf' : CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f - Λ ℓ • f = 0 :=
        hinj (by rw [hmem, map_zero])
      have hg' : CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN g - starRingEnd ℂ (Λ ℓ) • g = 0 := by
        apply hinjb
        rw [map_zero]
        have := h2
        rw [hmem, eq_comm, neg_eq_zero] at this
        exact this
      exact ⟨sub_eq_zero.mp hf', sub_eq_zero.mp hg'⟩
    by_cases hf0 : f = 0
    ·
      have hg0 : g ≠ 0 := by
        rintro rfl
        apply hx'0
        rw [← huv, hf0, map_zero, map_zero, add_zero]
      obtain ⟨conjF, hconjF⟩ := CuspForm.exists_qCoeff_conj N ((n : ℤ) + 2)
      have hgc0 : conjF g ≠ 0 := by
        intro h
        apply hg0
        refine eq_of_forall_qCoeff fun m => ?_
        have := hconjF g m
        rw [h] at this
        have h0 : starRingEnd ℂ (qCoeff g m) = 0 := by
          rw [← this, ← qCoeffLin_apply, map_zero]
        rw [← qCoeffLin_apply N _ m (0 : CuspForm (Gamma0 N) ((n : ℤ) + 2)), map_zero]
        exact (map_eq_zero_iff _ (RingHom.injective _)).mp h0
      refine conclude_of_cuspForm n S₀ Λ (conjF g) hgc0 fun ℓ hℓ hℓN hℓS => ?_
      have := heckeTLin_conj hℓ hℓN g (conjF g) (hconjF g) _ (hfg ℓ hℓ hℓN hℓS).2
      rwa [starRingEnd_self_apply] at this
    · exact conclude_of_cuspForm n S₀ Λ f hf0 fun ℓ hℓ hℓN hℓS => (hfg ℓ hℓ hℓN hℓS).1
  ·
    refine exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1 N n S₀ Λ x hpar
      fun ℓ hℓ hℓN hℓS => ?_
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    refine ⟨heckeH1 (isCompat N n ℓ), isCoeffHeckeOnH1_heckeH1 _, ?_⟩
    rw [heig ℓ hℓ hℓN hℓS, sub_self]
    exact Submodule.zero_mem _

end Main

end C3ESW1
p2m_reactivate "P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1.C3ESW1"

theorem solution (N : ℕ) [NeZero N] (n : ℕ)
    (S₀ : Set ℕ) (Λ : ℕ → ℂ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj ℂ n ℓ) S₀ Λ) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f :=
  C3ESW1.main N n S₀ Λ hocc

end S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1
end P2MW
export P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1 (solution)
