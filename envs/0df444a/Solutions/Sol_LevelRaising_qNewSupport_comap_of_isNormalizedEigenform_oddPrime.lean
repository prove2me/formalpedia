-- Prove2me | solution 1 for LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8990dd90-3135-56cd-9e24-b72f2152213f

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_HeckeWord
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_HeckeEis_DegeneracyTransfers
import Definitions.Def_IharaIota
import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
import Theorems.Thm_CuspForm_heckeWordHom_eq_zero_of_forall_newLattice
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector
import Theorems.Thm_HeckeEis_coresHom_eq_transfer
import Theorems.Thm_HeckeEis_coresHom_resHom_apply
import Theorems.Thm_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm
import Theorems.Thm_HeckeEis_heckeOperatorHom_commute
import Theorems.Thm_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel
import Theorems.Thm_HeckeEis_heckeOperatorHom_pullback_iota0
import Theorems.Thm_HeckeEis_heckeOperatorHom_pullback_iota1
import Theorems.Thm_HeckeEis_postcomp_heckeOperatorHom
import Theorems.Thm_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
import Theorems.Thm_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero
import Theorems.Thm_LevelRaising_exists_mem_range_of_forall_exists_add_dvd
import Theorems.Thm_LevelRaising_exists_parabolicPairings_perfect_mod_three
import Theorems.Thm_LevelRaising_moduleFinite_parabolicHoms_int
import Theorems.Thm_LevelRaising_nondegenerate_restrict_iSup_ker_pow
import Theorems.Thm_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff
import Theorems.Thm_ModularCurve_PDPairing_isFreeGroup_Gamma_four
import Theorems.Thm_ModularCurve_PDPairing_pairZFun_heckeT0_comm
import Theorems.Thm_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
import Theorems.Thm_ModularCurve_PDPairing_pairZ_nondegenerate_mod
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_ModularCurve_Period_exists_parabolicRealization
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Theorems.Thm_ModularCurve_index_heckeUpper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.iharaEdge_one"
p2m_attr_erase "simp" "Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply"

set_option Elab.async false
set_option autoImplicit false

open CongruenceSubgroup

namespace LRf

private noncomputable def wordValue (N q' : ℕ) [NeZero (N * q')] :
    FreeAlgebra ℤ ℕ →ₐ[ℤ] CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} :=
  (CuspForm.heckeWordForms (N * q') 2 {ℓ | ℓ ∣ N * q'}).codRestrict
    (CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'})
    (CuspForm.heckeWordForms_mem (N * q') 2 {ℓ | ℓ ∣ N * q'})

private theorem coe_wordValue (N q' : ℕ) [NeZero (N * q')] (P : FreeAlgebra ℤ ℕ) :
    ((wordValue N q' P : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}) :
        Module.End ℂ (CuspForm (Gamma0 (N * q')) 2)) =
      CuspForm.heckeWordForms (N * q') 2 {ℓ | ℓ ∣ N * q'} P := rfl

private theorem exists_wordValue_eq (N q' : ℕ) [NeZero (N * q')]
    (t : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}) :
    ∃ P : FreeAlgebra ℤ ℕ, wordValue N q' P = t := by
  obtain ⟨P, hP⟩ := CuspForm.exists_heckeWordForms_eq (N * q') 2 {ℓ | ℓ ∣ N * q'} t
  exact ⟨P, Subtype.ext hP⟩

end LRf

section Words
set_option autoImplicit false

open CongruenceSubgroup

namespace LRf

namespace Words

private theorem words_map_heckeWordHom {N M : ℕ} {A : Type*} [AddCommGroup A] (S : Set ℕ)
    [DecidablePred (· ∈ S)]
    (β : (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 M) →+ A))
    (hβ : ∀ (n : ℕ) [NeZero n], n.Prime → n ∉ S → ∀ φ : Additive (Gamma0 N) →+ A,
      β (HeckeEis.heckeOperatorHom N n A φ) = HeckeEis.heckeOperatorHom M n A (β φ))
    (P : FreeAlgebra ℤ ℕ) (φ : Additive (Gamma0 N) →+ A) :
    β (HeckeEis.heckeWordHom N A S P φ) = HeckeEis.heckeWordHom M A S P (β φ) := by
  induction P using FreeAlgebra.induction generalizing φ with
  | grade0 r =>
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply]
      exact map_zsmul β r φ
  | grade1 n =>
      by_cases h : n.Prime ∧ n ∉ S
      · haveI : NeZero n := ⟨h.1.ne_zero⟩
        rw [HeckeEis.heckeWordHom_ι_apply_of_prime h.1 h.2,
          HeckeEis.heckeWordHom_ι_apply_of_prime h.1 h.2]
        exact hβ n h.1 h.2 φ
      · rw [HeckeEis.heckeWordHom_ι, HeckeEis.heckeWordHom_ι, HeckeEis.heckeWordGenHom_of_not h,
          HeckeEis.heckeWordGenHom_of_not h, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  | mul a b ha hb =>
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

private theorem heckeWordHom_mem_parabolicHoms (L N q' : ℕ) (P : FreeAlgebra ℤ ℕ)
    (x : Additive (Gamma0 L) →+ ℤ) (hx : x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 L) ℤ) :
    HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'} P x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 L) ℤ := by
  induction P using FreeAlgebra.induction generalizing x with
  | grade0 r =>
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ r hx
  | grade1 n =>
      by_cases h : n.Prime ∧ n ∉ {ℓ | ℓ ∣ N * q'}
      · haveI : NeZero n := ⟨h.1.ne_zero⟩
        rw [HeckeEis.heckeWordHom_ι_apply_of_prime h.1 h.2, ModularCurve.Period.mem_parabolicHoms_iff]
        exact ModularCurve.Period.heckeOperatorHom_preserves_parabolic L n ℤ x
          (ModularCurve.Period.mem_parabolicHoms_iff.mp hx)
      · rw [HeckeEis.heckeWordHom_ι, HeckeEis.heckeWordGenHom_of_not h, LinearMap.zero_apply]
        exact Submodule.zero_mem _
  | mul a b ha hb =>
      rw [map_mul, Module.End.mul_apply]
      exact ha _ (hb _ hx)
  | add a b ha hb =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (ha _ hx) (hb _ hx)

private theorem heckeWordHom_comm_heckeOperatorHom (L N q' : ℕ) (P : FreeAlgebra ℤ ℕ) {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ.Prime) (x : Additive (Gamma0 L) →+ ℤ) :
    HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'} P (HeckeEis.heckeOperatorHom L ℓ ℤ x) =
      HeckeEis.heckeOperatorHom L ℓ ℤ (HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'} P x) := by
  exact (words_map_heckeWordHom {ℓ | ℓ ∣ N * q'} (HeckeEis.heckeOperatorHom L ℓ ℤ)
    (fun n _ hn _ φ => HeckeEis.heckeOperatorHom_commute L ℤ ⟨ℓ, hℓ⟩ ⟨n, hn⟩ φ) P x).symm

private theorem pullbackHom_iota0_heckeWordHom (N q' : ℕ) (P : FreeAlgebra ℤ ℕ) (φ : Additive (Gamma0 N) →+ ℤ) :
    HeckeEis.pullbackHom (Ihara.ι₀ N q') (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} P φ) =
      HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} P (HeckeEis.pullbackHom (Ihara.ι₀ N q') φ) := by
  exact words_map_heckeWordHom {ℓ | ℓ ∣ N * q'} (HeckeEis.pullbackHom (Ihara.ι₀ N q'))
    (fun n _ hn hnS ψ => HeckeEis.heckeOperatorHom_pullback_iota0 N q' n hn
      (fun hd => hnS (hd.mul_left N)) ψ) P φ

private theorem pullbackHom_iota1_heckeWordHom (N q' : ℕ) (P : FreeAlgebra ℤ ℕ) (φ : Additive (Gamma0 N) →+ ℤ) :
    HeckeEis.pullbackHom (Ihara.ι₁ N q') (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} P φ) =
      HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} P (HeckeEis.pullbackHom (Ihara.ι₁ N q') φ) := by
  exact words_map_heckeWordHom {ℓ | ℓ ∣ N * q'} (HeckeEis.pullbackHom (Ihara.ι₁ N q'))
    (fun n _ hn hnS ψ => HeckeEis.heckeOperatorHom_pullback_iota1 N q' n hn
      (fun hd => hnS (hd.mul_left N)) ψ) P φ

private theorem heckeWordHom_aeval_ι (L N q' : ℕ) {ℓ₀ : ℕ} [NeZero ℓ₀] (hℓ₀ : ℓ₀.Prime) (hℓ₀M : ¬ ℓ₀ ∣ N * q')
    (m : Polynomial ℤ) :
    HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'} (Polynomial.aeval (FreeAlgebra.ι ℤ ℓ₀) m) =
      Polynomial.aeval (HeckeEis.heckeOperatorHom L ℓ₀ ℤ).toIntLinearMap m := by
  have hS : ℓ₀ ∉ {ℓ | ℓ ∣ N * q'} := hℓ₀M
  have hgen : HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'} (FreeAlgebra.ι ℤ ℓ₀) =
      (HeckeEis.heckeOperatorHom L ℓ₀ ℤ).toIntLinearMap :=
    (HeckeEis.heckeWordHom_ι L ℤ {ℓ | ℓ ∣ N * q'} ℓ₀).trans (HeckeEis.heckeWordGenHom_of_prime hℓ₀ hS)
  rw [← hgen]
  exact (Polynomial.aeval_algHom_apply (HeckeEis.heckeWordHom L ℤ {ℓ | ℓ ∣ N * q'})
    (FreeAlgebra.ι ℤ ℓ₀) m).symm

private theorem aeval_comm_of_comm {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (β : A →+ B) (T : A →ₗ[ℤ] A) (T' : B →ₗ[ℤ] B) (h : ∀ x, β (T x) = T' (β x))
    (m : Polynomial ℤ) (x : A) :
    β (Polynomial.aeval T m x) = Polynomial.aeval T' m (β x) := by
  induction m using Polynomial.induction_on generalizing x with
  | C a =>
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply]
      exact map_zsmul β a x
  | add p q hp hq =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval T), map_mul (Polynomial.aeval T'),
        Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_comm_of_comm_left {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B]
    (β : A →+ B) (T : A →ₗ[ℤ] A) (T' : B →ₗ[ℤ] B) (h : ∀ x, β (T x) = T' (β x))
    (m : Polynomial ℤ) (x : A) :
    β (Polynomial.aeval T m x) = Polynomial.aeval T' m (β x) := by
  obtain rfl : ‹Module ℤ A› = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  exact aeval_comm_of_comm β T T' h m x

private theorem words_aeval_apply_comm {Λ : Type*} [AddCommGroup Λ] (T : Λ →ₗ[ℤ] Λ)
    (m : Polynomial ℤ) (v : Λ) :
    T (Polynomial.aeval T m v) = Polynomial.aeval T m (T v) := by
  have h : Polynomial.aeval T (Polynomial.X * m) v = Polynomial.aeval T (m * Polynomial.X) v := by
    rw [Polynomial.X_mul]
  rw [map_mul (Polynomial.aeval T), map_mul (Polynomial.aeval T), Polynomial.aeval_X,
    Module.End.mul_apply, Module.End.mul_apply] at h
  exact h

private theorem aeval_selfAdjoint {Λ : Type*} [AddCommGroup Λ] [Module ℤ Λ] (pair : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (T : Λ →ₗ[ℤ] Λ)
    (hadj : ∀ x y, pair (T x) y = pair x (T y)) (m : Polynomial ℤ) (x y : Λ) :
    pair (Polynomial.aeval T m x) y = pair x (Polynomial.aeval T m y) := by
  obtain rfl : ‹Module ℤ Λ› = AddCommGroup.toIntModule Λ := Subsingleton.elim _ _
  show pair (Polynomial.aeval T m x) y = pair x (Polynomial.aeval T m y)
  induction m using Polynomial.induction_on generalizing x y with
  | C a =>
      have hv : ∀ v : Λ, Polynomial.aeval T (Polynomial.C a) v = a • v := fun v => by
        rw [Polynomial.aeval_C]
        exact Module.algebraMap_end_apply ℤ ℤ Λ a v
      rw [hv, hv]
      exact (LinearMap.map_smul₂ pair a x y).trans (LinearMap.map_smul (pair x) a y).symm
  | add p q hp hq =>
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add,
        hp, hq]
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval T), Polynomial.aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, ih, hadj, words_aeval_apply_comm T]

private theorem exists_aeval_sub_eval_smul_eq {A : Type*} [AddCommGroup A] (T : A →ₗ[ℤ] A) (p e₀ : ℤ)
    (x : A) (hx : ∃ x', T x - e₀ • x = p • x') (m : Polynomial ℤ) :
    ∃ x', Polynomial.aeval T m x - (m.eval e₀) • x = p • x' := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨r, hr⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := e₀) (p := m)
  refine ⟨Polynomial.aeval T r x', ?_⟩
  have h1 : Polynomial.aeval T m x - (m.eval e₀) • x =
      Polynomial.aeval T (m - Polynomial.C (m.eval e₀)) x := by
    rw [map_sub, LinearMap.sub_apply, Polynomial.aeval_C, Module.algebraMap_end_apply]
  rw [h1, hr, mul_comm, map_mul (Polynomial.aeval T), Module.End.mul_apply, map_sub,
    LinearMap.sub_apply, Polynomial.aeval_X, Polynomial.aeval_C, Module.algebraMap_end_apply, hx']
  exact map_zsmul (Polynomial.aeval T r) p x'

end Words

end LRf

end Words

section Seed
set_option autoImplicit false

open CongruenceSubgroup

namespace LRf

namespace Seed

noncomputable section

open scoped MatrixGroups
open HeckeEis ModularCurve ModularCurve.Period

section WordLayer

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private theorem comp_heckeWordHom (L : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] (g : A →+ B)
    (P : FreeAlgebra ℤ ℕ) (φ : Additive (Gamma0 L) →+ A) :
    g.comp (heckeWordHom L A S P φ) = heckeWordHom L B S P (g.comp φ) := by
  induction P using FreeAlgebra.induction generalizing φ with
  | grade0 r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      exact AddMonoidHom.ext fun x => by simp
  | grade1 n =>
      by_cases h : n.Prime ∧ n ∉ S
      · rw [heckeWordHom_ι_apply_of_prime h.1 h.2, heckeWordHom_ι_apply_of_prime h.1 h.2]
        haveI : NeZero n := ⟨h.1.ne_zero⟩
        exact postcomp_heckeOperatorHom L n g φ
      · rw [heckeWordHom_ι, heckeWordHom_ι, heckeWordGenHom_of_not h, heckeWordGenHom_of_not h]
        exact AddMonoidHom.ext fun x => by simp
  | mul a b ha hb =>
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, AddMonoidHom.comp_add, ha, hb]

private theorem isParabolicHom_heckeWordHom (L : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (P : FreeAlgebra ℤ ℕ) :
    ∀ φ : Additive (Gamma0 L) →+ A, IsParabolicHom (Gamma0 L) φ →
      IsParabolicHom (Gamma0 L) (heckeWordHom L A S P φ) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
      intro φ hφ γ hγ
      simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      show r • φ (Additive.ofMul γ) = 0
      rw [hφ γ hγ]
      exact smul_zero r
  | grade1 n =>
      intro φ hφ
      by_cases h : n.Prime ∧ n ∉ S
      · rw [heckeWordHom_ι_apply_of_prime h.1 h.2]
        haveI : NeZero n := ⟨h.1.ne_zero⟩
        exact heckeOperatorHom_preserves_parabolic L n A φ hφ
      · rw [heckeWordHom_ι, heckeWordGenHom_of_not h, LinearMap.zero_apply]
        intro γ _
        rfl
  | mul a b ha hb =>
      intro φ hφ
      rw [map_mul, Module.End.mul_apply]
      exact ha _ (hb _ hφ)
  | add a b ha hb =>
      intro φ hφ γ hγ
      rw [map_add, LinearMap.add_apply]
      show heckeWordHom L A S a φ (Additive.ofMul γ) + heckeWordHom L A S b φ (Additive.ofMul γ) = 0
      rw [ha φ hφ γ hγ, hb φ hφ γ hγ, add_zero]

end WordLayer

private theorem smul_eq_mulLeft_comp {L : ℕ} (c : ℂ) (θ : Additive (Gamma0 L) →+ ℂ) :
    c • θ = (AddMonoidHom.mulLeft c).comp θ := by
  ext x
  rfl

private def wordScalar (N q' : ℕ) [NeZero (N * q')]
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ) :
    FreeAlgebra ℤ ℕ →+* ℂ :=
  (algebraMap (integralClosure ℤ ℂ) ℂ).comp (χ₁.comp (wordValue N q').toRingHom)

private theorem wordScalar_apply (N q' : ℕ) [NeZero (N * q')]
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ) (P : FreeAlgebra ℤ ℕ) :
    wordScalar N q' χ₁ P = ((χ₁ (wordValue N q' P) : integralClosure ℤ ℂ) : ℂ) := rfl

private theorem heckeWordHom_smul_realisation {N q' : ℕ} [NeZero (N * q')]
    {f : CuspForm (Gamma0 N) 2} (hint : f.PrimeCoeffsIntegral)
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (hχ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
      ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff f ℓ)
    (f₀ : Additive (Gamma0 N) →+ ℂ)
    (heig : ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
      heckeOperatorHom N ℓ ℂ f₀ = ((CuspForm.eigenLift hint ⟨ℓ, hℓp⟩ : integralClosure ℤ ℂ) : ℂ) • f₀)
    (P : FreeAlgebra ℤ ℕ) (c : ℂ) :
    heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'} P (c • f₀) = (c * wordScalar N q' χ₁ P) • f₀ := by
  induction P using FreeAlgebra.induction generalizing c with
  | grade0 r =>
      have h := eq_intCast ((wordScalar N q' χ₁).comp (algebraMap ℤ (FreeAlgebra ℤ ℕ))) r
      rw [RingHom.comp_apply] at h
      rw [h]
      simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      rw [mul_comm, ← smul_smul]
      exact (Int.cast_smul_eq_zsmul ℂ r (c • f₀)).symm
  | grade1 n =>
      by_cases h : n.Prime ∧ n ∉ {ℓ | ℓ ∣ N * q'}
      · have hnM : ¬ n ∣ N * q' := h.2
        haveI : NeZero n := ⟨h.1.ne_zero⟩
        have hT : wordValue N q' (FreeAlgebra.ι ℤ n) = CuspForm.heckeAlgebra.T h.1 hnM hnM :=
          Subtype.ext ((coe_wordValue N q' _).trans ((CuspForm.heckeWordForms_ι _ _ _ n).trans
            (CuspForm.heckeWordGenForms_of_not_dvd h.1 hnM h.2)))
        have hval : wordScalar N q' χ₁ (FreeAlgebra.ι ℤ n)
            = ((CuspForm.eigenLift hint ⟨n, h.1⟩ : integralClosure ℤ ℂ) : ℂ) := by
          rw [wordScalar_apply, hT, hχ₁ n h.1 hnM, CuspForm.eigenLift_coe]
        rw [heckeWordHom_ι_apply_of_prime h.1 h.2, smul_eq_mulLeft_comp c f₀, ← postcomp_heckeOperatorHom,
          heig n inferInstance h.1, ← smul_eq_mulLeft_comp, smul_smul, hval]
      · have hT0 : wordValue N q' (FreeAlgebra.ι ℤ n) = 0 :=
          Subtype.ext ((coe_wordValue N q' _).trans ((CuspForm.heckeWordForms_ι _ _ _ n).trans
            (CuspForm.heckeWordGenForms_of_not h)))
        have hval0 : wordScalar N q' χ₁ (FreeAlgebra.ι ℤ n) = 0 := by
          show algebraMap (integralClosure ℤ ℂ) ℂ (χ₁ (wordValue N q' (FreeAlgebra.ι ℤ n))) = 0
          rw [hT0, map_zero, map_zero]
        rw [heckeWordHom_ι, heckeWordGenHom_of_not h, LinearMap.zero_apply, hval0, mul_zero, zero_smul]
  | mul a b ha hb =>
      rw [map_mul (heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'}), Module.End.mul_apply, hb, ha,
        map_mul (wordScalar N q' χ₁)]
      congr 1
      ring
  | add a b ha hb =>
      rw [map_add (heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'}), LinearMap.add_apply, ha, hb,
        map_add (wordScalar N q' χ₁), mul_add, add_smul]

private theorem heckeWordHom_realisation {N q' : ℕ} [NeZero (N * q')]
    {f : CuspForm (Gamma0 N) 2} (hint : f.PrimeCoeffsIntegral)
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (hχ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
      ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff f ℓ)
    (f₀ : Additive (Gamma0 N) →+ ℂ)
    (heig : ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
      heckeOperatorHom N ℓ ℂ f₀ = ((CuspForm.eigenLift hint ⟨ℓ, hℓp⟩ : integralClosure ℤ ℂ) : ℂ) • f₀)
    (P : FreeAlgebra ℤ ℕ) :
    heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'} P f₀ = ((χ₁ (wordValue N q' P) : integralClosure ℤ ℂ) : ℂ) • f₀ := by
  have h := heckeWordHom_smul_realisation hint χ₁ hχ₁ f₀ heig P 1
  rwa [one_smul, one_mul, wordScalar_apply] at h

section Lattice

variable {X : Type*} [AddCommGroup X] {n : ℕ}

private theorem map_sum_zsmul_eq_sum_mulVec_zsmul {F : Type*} [FunLike F X X] [AddMonoidHomClass F X X]
    (T : F) (e : Fin n → X)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ j, T (e j) = ∑ i, A i j • e i) (k : Fin n → ℤ) :
    T (∑ j, k j • e j) = ∑ i, (A.mulVec k) i • e i := by
  simp only [map_sum, map_zsmul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

private theorem exists_eq_natCast_smul_of_forall_cast_eq_zero {p : ℕ} (c : Fin n → ℤ)
    (h : ∀ i, (c i : ZMod p) = 0) : ∃ k : Fin n → ℤ, c = (p : ℤ) • k := by
  have hd : ∀ i, (p : ℤ) ∣ c i := fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (h i)
  choose k hk using hd
  exact ⟨k, funext fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact hk i⟩

private theorem exists_sub_zsmul_eq_natCast_smul {F : Type*} [FunLike F X X] [AddMonoidHomClass F X X]
    (T : F) (e : Fin n → X)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ j, T (e j) = ∑ i, A i j • e i) (k : Fin n → ℤ)
    (c : ℤ) {p : ℕ} (h : ∀ i, (((A.mulVec k) i - c * k i : ℤ) : ZMod p) = 0) :
    ∃ ψ : X, T (∑ j, k j • e j) - c • (∑ j, k j • e j) = (p : ℤ) • ψ := by
  obtain ⟨k', hk'⟩ := exists_eq_natCast_smul_of_forall_cast_eq_zero _ h
  refine ⟨∑ i, k' i • e i, ?_⟩
  rw [map_sum_zsmul_eq_sum_mulVec_zsmul T e A hA, Finset.smul_sum, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← sub_smul, smul_smul]
  congr 1
  exact congrFun hk' i

private theorem forall_cast_mulVec_sub_eq_zero {p : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ)
    (c : ℤ) (h : (A.map (Int.cast : ℤ → ZMod p)).mulVec (fun i => (k i : ZMod p))
      = ((c : ZMod p) • fun i => (k i : ZMod p))) :
    ∀ i, (((A.mulVec k) i - c * k i : ℤ) : ZMod p) = 0 := by
  intro i
  have hi := congrFun h i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [Matrix.mulVec, dotProduct]
  push_cast
  rw [hi, sub_self]

private theorem castAddHom_comp_ne_zero {Γ : Subgroup SL(2, ℤ)}
    (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)) {p : ℕ}
    (k : Fin n → ℤ) (hk : ∃ j, (k j : ZMod p) ≠ 0) :
    (Int.castAddHom (ZMod p)).comp
      ((∑ j, k j • b j : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) ≠ 0 := by
  intro h0
  obtain ⟨x', hx'⟩ := (LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff _).1 h0
  obtain ⟨j, hj⟩ := hk
  apply hj
  have e1 : b.equivFun (∑ i, k i • b i) = k := by
    rw [← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  have e2 := congrArg (fun y => b.equivFun y j) hx'
  simp only [e1, map_zsmul, Pi.smul_apply, smul_eq_mul] at e2
  rw [e2]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

private theorem coe_sum_zsmul {Γ : Subgroup SL(2, ℤ)}
    (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)) (k : Fin n → ℤ) :
    ((∑ j, k j • b j : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)
      = ∑ j, k j • (b j : Additive Γ →+ ℤ) := by
  simp only [Submodule.coe_sum, Submodule.coe_smul]

end Lattice

private def endC {N : ℕ} (TC : (Additive (Gamma0 N) →+ ℂ) → (Additive (Gamma0 N) →+ ℂ))
    (hTC : ∀ x, IsParabolicHom (Gamma0 N) x → IsParabolicHom (Gamma0 N) (TC x))
    (hadd : ∀ x y, TC (x + y) = TC x + TC y)
    (hsmul : ∀ (c : ℂ) (x : Additive (Gamma0 N) →+ ℂ), TC (c • x) = c • TC x) :
    ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ →ₗ[ℂ]
      ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ where
  toFun φ := ⟨TC (φ : Additive (Gamma0 N) →+ ℂ), hTC _ φ.2⟩
  map_add' φ ψ := by
    refine Subtype.ext ?_
    show TC ((φ : Additive (Gamma0 N) →+ ℂ) + ψ) = _
    rw [hadd]; rfl
  map_smul' c φ := by
    refine Subtype.ext ?_
    show TC (c • (φ : Additive (Gamma0 N) →+ ℂ)) = c • TC (φ : Additive (Gamma0 N) →+ ℂ)
    exact hsmul c φ

private theorem endC_coe {N : ℕ} (TC : (Additive (Gamma0 N) →+ ℂ) → (Additive (Gamma0 N) →+ ℂ))
    (hTC : ∀ x, IsParabolicHom (Gamma0 N) x → IsParabolicHom (Gamma0 N) (TC x))
    (hadd : ∀ x y, TC (x + y) = TC x + TC y)
    (hsmul : ∀ (c : ℂ) (x : Additive (Gamma0 N) →+ ℂ), TC (c • x) = c • TC x)
    (φ : ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ) :
    ((endC TC hTC hadd hsmul φ : ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ) :
      Additive (Gamma0 N) →+ ℂ) = TC φ := rfl

private theorem exists_matrix_of_eigen {N t : ℕ}
    (b : Module.Basis (Fin t) ℤ (ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ))
    (bC : Module.Basis (Fin t) ℂ (ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ))
    (hbC : ∀ i, (bC i : Additive (Gamma0 N) →+ ℂ) = (Int.castAddHom ℂ).comp (b i : Additive (Gamma0 N) →+ ℤ))
    (T : (Additive (Gamma0 N) →+ ℤ) → (Additive (Gamma0 N) →+ ℤ))
    (hT : ∀ x, IsParabolicHom (Gamma0 N) x → IsParabolicHom (Gamma0 N) (T x))
    (TC : (Additive (Gamma0 N) →+ ℂ) → (Additive (Gamma0 N) →+ ℂ))
    (hTC : ∀ x, IsParabolicHom (Gamma0 N) x → IsParabolicHom (Gamma0 N) (TC x))
    (hadd : ∀ x y, TC (x + y) = TC x + TC y)
    (hsmul : ∀ (c : ℂ) (x : Additive (Gamma0 N) →+ ℂ), TC (c • x) = c • TC x)
    (hcomp : ∀ x, (Int.castAddHom ℂ).comp (T x) = TC ((Int.castAddHom ℂ).comp x))
    (f₀ : ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ) (a : ℂ)
    (heig : TC (f₀ : Additive (Gamma0 N) →+ ℂ) = a • (f₀ : Additive (Gamma0 N) →+ ℂ)) :
    ∃ A : Matrix (Fin t) (Fin t) ℤ,
      (∀ j, T (b j : Additive (Gamma0 N) →+ ℤ) = ∑ i, A i j • (b i : Additive (Gamma0 N) →+ ℤ)) ∧
      (A.map (Int.cast : ℤ → ℂ)).mulVec (bC.equivFun f₀) = a • bC.equivFun f₀ := by
  classical

  have memZ : ∀ j, T (b j : Additive (Gamma0 N) →+ ℤ) ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
    fun j => hT _ (b j).2
  let A : Matrix (Fin t) (Fin t) ℤ := fun i j => b.repr ⟨_, memZ j⟩ i
  have hAZ : ∀ j, T (b j : Additive (Gamma0 N) →+ ℤ) = ∑ i, A i j • (b i : Additive (Gamma0 N) →+ ℤ) := by
    intro j
    have h := b.sum_repr ⟨_, memZ j⟩
    have h' := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    exact h'.symm
  refine ⟨A, hAZ, ?_⟩

  have hAC : ∀ j, endC TC hTC hadd hsmul (bC j) = ∑ i, ((A i j : ℤ) : ℂ) • bC i := by
    intro j
    refine Subtype.ext ?_
    rw [endC_coe, hbC j, ← hcomp, hAZ j]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    refine AddMonoidHom.ext fun x => ?_
    simp [AddMonoidHom.finsetSum_apply, hbC]

  have heq : endC TC hTC hadd hsmul f₀ = a • f₀ := by
    refine Subtype.ext ?_
    rw [endC_coe, Submodule.coe_smul, heig]
  have hf₀sum : f₀ = ∑ j, bC.equivFun f₀ j • bC j := (bC.sum_equivFun f₀).symm
  have lhs : endC TC hTC hadd hsmul f₀ = ∑ i, (∑ j, ((A i j : ℤ) : ℂ) * bC.equivFun f₀ j) • bC i := by
    conv_lhs => rw [hf₀sum]
    rw [map_sum]
    simp only [map_smul, hAC, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have rhs : a • f₀ = ∑ i, (a * bC.equivFun f₀ i) • bC i := by
    conv_lhs => rw [hf₀sum]
    rw [Finset.smul_sum]
    simp only [smul_smul]
  have hcoef : (fun i => ∑ j, ((A i j : ℤ) : ℂ) * bC.equivFun f₀ j) = fun i => a * bC.equivFun f₀ i := by
    have h1 := lhs.symm.trans (heq.trans rhs)
    rw [← bC.equivFun_symm_apply, ← bC.equivFun_symm_apply] at h1
    exact bC.equivFun.symm.injective h1
  funext i
  have := congrFun hcoef i
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this

end

private theorem exists_seed
    {N q' : ℕ} [NeZero N] [NeZero (N * q')] [NeZero q'] (hq' : q'.Prime)
    {f : CuspForm (Gamma0 N) 2} (hf : CuspForm.IsNormalizedEigenform f)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal)
    (p : ℕ) [Fact p.Prime] (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (hχ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
      ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff f ℓ)
    (aq : integralClosure ℤ ℂ) (haq : (aq : ℂ) = ModularFormClass.qCoeff f q')
    (c : ℤ) (hc : (c : integralClosure ℤ ℂ) - aq ∈ 𝔪)
    (r : ℕ) (ws : ℕ → FreeAlgebra ℤ ℕ) (hws : ∀ i, i < r → χ₁ (wordValue N q' (ws i)) ∈ 𝔪) :
    ∃ φ₀ : Additive (Gamma0 N) →+ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ ∧
      (Int.castAddHom (ZMod p)).comp φ₀ ≠ 0 ∧
      (∀ i, i < r → ∃ ψ : Additive (Gamma0 N) →+ ℤ,
        HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i) φ₀ = (p : ℤ) • ψ) ∧
      (∃ ψ : Additive (Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N q' ℤ φ₀ - c • φ₀ = (p : ℤ) • ψ) := by
  classical
  have hint : f.PrimeCoeffsIntegral := hf.primeCoeffsIntegral_of_neZero
  have hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪 := by exact_mod_cast hp𝔪
  have aq_eq : aq = CuspForm.eigenLift hint ⟨q', hq'⟩ := by
    apply Subtype.ext
    rw [CuspForm.eigenLift_coe, haq]

  obtain ⟨t, b, hK⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (Gamma0 N)
  obtain ⟨bC, hbC⟩ := hK ℂ

  obtain ⟨f₀, hf₀, heig⟩ := ModularCurve.Period.exists_parabolicRealization N f hf hint ℂ
    (algebraMap (integralClosure ℤ ℂ) ℂ)
  have heig' : ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
      HeckeEis.heckeOperatorHom N ℓ ℂ (f₀ : Additive (Gamma0 N) →+ ℂ)
        = ((CuspForm.eigenLift hint ⟨ℓ, hℓp⟩ : integralClosure ℤ ℂ) : ℂ) • (f₀ : Additive (Gamma0 N) →+ ℂ) :=
    fun ℓ hℓ0 hℓp => heig ℓ hℓ0 hℓp
  have hv0 : bC.equivFun f₀ ≠ 0 := by
    intro h
    apply hf₀
    have : bC.equivFun f₀ = bC.equivFun 0 := by rw [map_zero]; exact h
    exact bC.equivFun.injective this

  have hword : ∀ i : Fin r, ∃ A : Matrix (Fin t) (Fin t) ℤ,
      (∀ j, HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i) (b j : Additive (Gamma0 N) →+ ℤ)
          = ∑ i', A i' j • (b i' : Additive (Gamma0 N) →+ ℤ)) ∧
      (A.map (Int.cast : ℤ → ℂ)).mulVec (bC.equivFun f₀)
        = ((χ₁ (wordValue N q' (ws i)) : integralClosure ℤ ℂ) : ℂ) • bC.equivFun f₀ := fun i =>
    exists_matrix_of_eigen b bC hbC
      (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i))
      (isParabolicHom_heckeWordHom N {ℓ | ℓ ∣ N * q'} (ws i))
      (HeckeEis.heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'} (ws i))
      (isParabolicHom_heckeWordHom N {ℓ | ℓ ∣ N * q'} (ws i))
      (fun x y => map_add (HeckeEis.heckeWordHom N ℂ {ℓ | ℓ ∣ N * q'} (ws i)) x y)
      (fun z x => by rw [smul_eq_mulLeft_comp, smul_eq_mulLeft_comp, comp_heckeWordHom])
      (fun x => comp_heckeWordHom N {ℓ | ℓ ∣ N * q'} (Int.castAddHom ℂ) (ws i) x)
      f₀ _ (heckeWordHom_realisation hint χ₁ hχ₁ _ heig' (ws i))
  choose Aw hAw heigw using hword
  obtain ⟨Aq, hAq, heigq⟩ := exists_matrix_of_eigen b bC hbC
      (HeckeEis.heckeOperatorHom N q' ℤ)
      (fun x hx => ModularCurve.Period.heckeOperatorHom_preserves_parabolic N q' ℤ x hx)
      (HeckeEis.heckeOperatorHom N q' ℂ)
      (fun x hx => ModularCurve.Period.heckeOperatorHom_preserves_parabolic N q' ℂ x hx)
      (fun x y => map_add (HeckeEis.heckeOperatorHom N q' ℂ) x y)
      (fun z x => by rw [smul_eq_mulLeft_comp, smul_eq_mulLeft_comp, HeckeEis.postcomp_heckeOperatorHom])
      (fun x => HeckeEis.postcomp_heckeOperatorHom N q' (Int.castAddHom ℂ) x)
      f₀ _ (heig' q' inferInstance hq')

  obtain ⟨m, hm_ne, hm_eig⟩ :=
    DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector (I := Fin r ⊕ Unit)
      (fun i => Sum.elim Aw (fun _ => Aq) i) (p := p) h𝔪.isPrime hp𝔪'
      (α := Sum.elim (fun i => χ₁ (wordValue N q' (ws i))) (fun _ => CuspForm.eigenLift hint ⟨q', hq'⟩))
      (v := bC.equivFun f₀) hv0
      (fun i => by
        cases i with
        | inl i => exact heigw i
        | inr _ => exact heigq)
      (n := Sum.elim (fun _ => (0 : ℤ)) (fun _ => c))
      (fun i => by
        cases i with
        | inl i =>
            show χ₁ (wordValue N q' (ws i)) - ((0 : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪
            rw [Int.cast_zero, sub_zero]
            exact hws i i.2
        | inr _ =>
            show CuspForm.eigenLift hint ⟨q', hq'⟩ - (c : integralClosure ℤ ℂ) ∈ 𝔪
            rw [← aq_eq, show aq - (c : integralClosure ℤ ℂ) = -((c : integralClosure ℤ ℂ) - aq) from
              (neg_sub _ _).symm]
            exact neg_mem hc)

  let mL : Fin t → ℤ := fun i => (m i).val
  have hmL_cast : (fun i => (mL i : ZMod p)) = m := by
    funext i
    show ((((m i).val : ℕ) : ℤ) : ZMod p) = m i
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  have hmL_ex : ∃ j, (mL j : ZMod p) ≠ 0 := by
    by_contra h
    push Not at h
    exact hm_ne (funext fun j => by rw [← hmL_cast]; exact h j)

  refine ⟨((∑ j, mL j • b j : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) : Additive (Gamma0 N) →+ ℤ),
    (∑ j, mL j • b j).2, castAddHom_comp_ne_zero b mL hmL_ex, ?_, ?_⟩
  ·
    intro i hi
    rw [coe_sum_zsmul b mL]
    obtain ⟨ψ, hψ⟩ := exists_sub_zsmul_eq_natCast_smul (p := p)
      (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i))
      (fun j => (b j : Additive (Gamma0 N) →+ ℤ)) (Aw ⟨i, hi⟩) (hAw ⟨i, hi⟩) mL 0
      (forall_cast_mulVec_sub_eq_zero (p := p) (Aw ⟨i, hi⟩) mL 0
        (by rw [hmL_cast]; exact hm_eig (Sum.inl ⟨i, hi⟩)))
    refine ⟨ψ, ?_⟩
    rw [zero_smul ℤ, sub_zero] at hψ
    exact hψ
  ·
    rw [coe_sum_zsmul b mL]
    refine exists_sub_zsmul_eq_natCast_smul (HeckeEis.heckeOperatorHom N q' ℤ)
      (fun j => (b j : Additive (Gamma0 N) →+ ℤ)) Aq hAq mL c ?_
    refine forall_cast_mulVec_sub_eq_zero Aq mL c ?_
    rw [hmL_cast]
    exact hm_eig (Sum.inr ())

end Seed

end LRf

end Seed

section Engine

set_option Elab.async false
set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace LRf
namespace Engine

section L1a

private def IntPSaturated {V : Type*} [AddCommGroup V] (S : AddSubgroup V) (p : ℤ) : Prop :=
  ∀ v : V, p • v ∈ S → v ∈ S

private theorem parabolicHoms_int_saturated {Γ : Subgroup SL(2, ℤ)} {p : ℤ} (hp : p ≠ 0) :
    IntPSaturated (ModularCurve.Period.parabolicHoms ℤ Γ ℤ).toAddSubgroup p := by
  intro ψ hψ γ hγ
  have h : p * ψ (Additive.ofMul γ) = 0 := hψ γ hγ
  exact (mul_eq_zero.mp h).resolve_left hp

end L1a

section L1d

noncomputable section

variable {V : Type*} [AddCommGroup V] (p : ℕ)

private def intPTop : AddSubgroup V := AddMonoidHom.range ((p : ℤ) • (AddMonoidHom.id V))

private theorem mem_intPTop_iff {v : V} : v ∈ intPTop (V := V) p ↔ ∃ w, v = (p : ℤ) • w := by
  unfold intPTop
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

private abbrev QuotPTop := V ⧸ intPTop (V := V) p

private scoped instance : Module (ZMod p) (QuotPTop (V := V) p) :=
  QuotientAddGroup.zmodModule (fun x => (mem_intPTop_iff p).mpr
    ⟨x, by rw [natCast_zsmul]⟩)

variable (B : LinearMap.BilinForm ℤ V)

private def castCompB : V →+ V →+ ZMod p where
  toFun v := ⟨⟨fun w => (B v w : ZMod p), by simp⟩, fun a b => by simp⟩
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp

private def reductionModInner (v : V) : QuotPTop (V := V) p →+ ZMod p :=
  QuotientAddGroup.lift (intPTop p) (castCompB p B v) (by
    intro w hw
    obtain ⟨w', rfl⟩ := (mem_intPTop_iff p).mp hw
    show ((B v ((p : ℤ) • w') : ℤ) : ZMod p) = 0
    simp)

private lemma reductionModInner_mk (v w : V) :
    reductionModInner p B v (QuotientAddGroup.mk w) = (B v w : ZMod p) := rfl

private def reductionModAddHom : QuotPTop (V := V) p →+ QuotPTop (V := V) p →+ ZMod p :=
  QuotientAddGroup.lift (intPTop p)
    { toFun := reductionModInner p B
      map_zero' := by ext w; simp [reductionModInner_mk]
      map_add' := fun a b => by ext w; simp [reductionModInner_mk] }
    (by
      intro v hv
      obtain ⟨v', rfl⟩ := (mem_intPTop_iff p).mp hv
      ext w
      show ((B ((p : ℤ) • v') w : ℤ) : ZMod p) = 0
      simp)

private def reductionMod : LinearMap.BilinForm (ZMod p) (QuotPTop (V := V) p) where
  toFun x := (reductionModAddHom p B x).toZModLinearMap p
  map_add' x y := by ext z; simp
  map_smul' c x := by
    ext z
    exact ZMod.map_smul
      (AddMonoidHom.eval z |>.comp (reductionModAddHom p B)) c x

@[scoped simp] private lemma reductionMod_mk_mk (v w : V) :
    reductionMod p B (QuotientAddGroup.mk v) (QuotientAddGroup.mk w) = (B v w : ZMod p) :=
  rfl

private theorem separatingLeft_reductionMod_iff :
    (reductionMod p B).SeparatingLeft
      ↔ ∀ x : V, (∀ y : V, (p : ℤ) ∣ B x y) → ∃ x' : V, x = (p : ℤ) • x' := by
  constructor
  · intro hsep x hdvd
    have h0 := hsep (QuotientAddGroup.mk x) (fun y => by
      obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hdvd w))
    exact (mem_intPTop_iff p).mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  · intro hperf x hx
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hdvd : ∀ w, (p : ℤ) ∣ B v w := fun w => by
      have := hx (QuotientAddGroup.mk w)
      simpa [reductionMod_mk_mk, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    obtain ⟨v', rfl⟩ := hperf v hdvd
    exact (QuotientAddGroup.eq_zero_iff _).mpr ((mem_intPTop_iff p).mpr ⟨v', rfl⟩)

private theorem separatingRight_reductionMod_iff :
    (reductionMod p B).SeparatingRight
      ↔ ∀ y : V, (∀ x : V, (p : ℤ) ∣ B x y) → ∃ y' : V, y = (p : ℤ) • y' := by
  constructor
  · intro hsep y hdvd
    have h0 := hsep (QuotientAddGroup.mk y) (fun x => by
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hdvd v))
    exact (mem_intPTop_iff p).mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  · intro hperf y hy
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hdvd : ∀ v, (p : ℤ) ∣ B v w := fun v => by
      have := hy (QuotientAddGroup.mk v)
      simpa [reductionMod_mk_mk, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    obtain ⟨w', rfl⟩ := hperf w hdvd
    exact (QuotientAddGroup.eq_zero_iff _).mpr ((mem_intPTop_iff p).mpr ⟨w', rfl⟩)

end

end L1d

section L1b

noncomputable section

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] (p : ℕ)

private def reductionModHom (φ : V →ₗ[ℤ] W) : QuotPTop (V := V) p →ₗ[ZMod p] QuotPTop (V := W) p :=
  (QuotientAddGroup.map (intPTop (V := V) p) (intPTop (V := W) p) φ.toAddMonoidHom (by
    intro v hv
    obtain ⟨v', rfl⟩ := (mem_intPTop_iff p).mp hv
    exact (mem_intPTop_iff p).mpr ⟨φ v', by simp⟩)).toZModLinearMap p

@[scoped simp] private lemma reductionModHom_mk (φ : V →ₗ[ℤ] W) (v : V) :
    reductionModHom p φ (QuotientAddGroup.mk v) = QuotientAddGroup.mk (φ v) :=
  rfl

private abbrev reductionModEnd (T : V →ₗ[ℤ] V) : Module.End (ZMod p) (QuotPTop (V := V) p) :=
  reductionModHom p T

private lemma reductionModEnd_mk (T : V →ₗ[ℤ] V) (v : V) :
    reductionModEnd p T (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v) :=
  rfl

private theorem reductionModHom_comp_of_comp (φ : V →ₗ[ℤ] W) (g : V →ₗ[ℤ] V) (g' : W →ₗ[ℤ] W)
    (h : φ ∘ₗ g = g' ∘ₗ φ) :
    reductionModHom p φ ∘ₗ reductionModEnd p g = reductionModEnd p g' ∘ₗ reductionModHom p φ := by
  ext x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [LinearMap.comp_apply, reductionModHom_mk]
  exact congrArg QuotientAddGroup.mk (LinearMap.congr_fun h v)

variable (B : LinearMap.BilinForm ℤ V)

private theorem reductionMod_reductionModHom_selfAdjoint (T : V →ₗ[ℤ] V)
    (hadj : ∀ x y : V, B (T x) y = B x (T y)) :
    ∀ x y : QuotPTop (V := V) p,
      reductionMod p B (reductionModEnd p T x) y = reductionMod p B x (reductionModEnd p T y) := by
  intro x y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [reductionModEnd_mk, reductionMod_mk_mk, hadj v w]

variable {V₀ : Type*} [AddCommGroup V₀] (B₀ : LinearMap.BilinForm ℤ V₀)

private theorem reductionMod_adj_of_adj (α : V₀ →ₗ[ℤ] V) (β : V →ₗ[ℤ] V₀)
    (hproj : ∀ (x : V) (y : V₀), B₀ (β x) y = B x (α y)) :
    ∀ (x : QuotPTop (V := V) p) (y : QuotPTop (V := V₀) p),
      reductionMod p B₀ (reductionModHom p β x) y
        = reductionMod p B x (reductionModHom p α y) := by
  intro x y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [reductionModHom_mk, reductionMod_mk_mk, hproj v w]

end

end L1b

section L2

open Module LinearMap

variable {F V V' : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

private theorem mem_iSup_ker_pow_iff (g : Module.End F V) (x : V) :
    x ∈ (⨆ n : ℕ, LinearMap.ker (g ^ n)) ↔ ∃ n : ℕ, (g ^ n) x = 0 := by
  have hdir : Directed (· ≤ ·) (fun n : ℕ => LinearMap.ker (g ^ n)) :=
    Monotone.directed_le fun m n h => by simpa using g.iterateKer.monotone h
  rw [Submodule.mem_iSup_of_directed _ hdir]
  simp [LinearMap.mem_ker]

private theorem map_mem_iSup_ker_pow (g : Module.End F V) (g' : Module.End F V') (φ : V →ₗ[F] V')
    (hφ : ∀ x, φ (g x) = g' (φ x)) {x : V} (hx : x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n)) :
    φ x ∈ ⨆ n : ℕ, LinearMap.ker (g' ^ n) := by
  obtain ⟨n, hn⟩ := (mem_iSup_ker_pow_iff g x).mp hx
  refine (mem_iSup_ker_pow_iff g' (φ x)).mpr ⟨n, ?_⟩
  have key : ∀ m : ℕ, ∀ v : V, φ ((g ^ m) v) = (g' ^ m) (φ v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih => intro v; rw [pow_succ, Module.End.mul_apply, ih, hφ, ← Module.End.mul_apply,
        ← pow_succ]
  rw [← key, hn, map_zero]

private theorem eq_zero_of_mem_iSup_ker_pow_of_apply_eq_smul (g : Module.End F V) {μ : F} (hμ : μ ≠ 0)
    {x : V} (hx : x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n)) (heig : g x = μ • x) : x = 0 := by
  obtain ⟨n, hn⟩ := (mem_iSup_ker_pow_iff g x).mp hx
  have hscale : ∀ k : ℕ, (g ^ k) x = (μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, heig, map_smul, ih, smul_smul, ← pow_succ']
  have h0 : (μ ^ n) • x = 0 := by rw [← hscale n]; exact hn
  exact (smul_eq_zero.mp h0).resolve_left (pow_ne_zero n hμ)

end L2

section L2b

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem restrict_iSup_ker_pow_nondegenerate [FiniteDimensional F V] (B : LinearMap.BilinForm F V)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) (hBr : ∀ y, (∀ x, B x y = 0) → y = 0)
    (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) :
    (∀ x : ↥(⨆ n : ℕ, LinearMap.ker (g ^ n)),
        (∀ y : ↥(⨆ n : ℕ, LinearMap.ker (g ^ n)),
          B.restrict (⨆ n : ℕ, LinearMap.ker (g ^ n)) x y = 0) → x = 0) ∧
      (∀ y : ↥(⨆ n : ℕ, LinearMap.ker (g ^ n)),
        (∀ x : ↥(⨆ n : ℕ, LinearMap.ker (g ^ n)),
          B.restrict (⨆ n : ℕ, LinearMap.ker (g ^ n)) x y = 0) → y = 0) := by
  obtain ⟨hl, hr⟩ := LevelRaising.nondegenerate_restrict_iSup_ker_pow B hBl hBr g hadj
  refine ⟨fun x hx => Subtype.ext (hl x.1 x.2 fun y hy => ?_),
    fun y hy => Subtype.ext (hr y.1 y.2 fun x hx => ?_)⟩
  · exact hx ⟨y, hy⟩
  · exact hy ⟨x, hx⟩

private theorem map_mem_iSup_ker_pow' {V' : Type*} [AddCommGroup V'] [Module F V'] (g : Module.End F V)
    (g' : Module.End F V') (φ : V →ₗ[F] V') (hφ : φ ∘ₗ g = g' ∘ₗ φ) {x : V}
    (hx : x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n)) : φ x ∈ ⨆ n : ℕ, LinearMap.ker (g' ^ n) :=
  map_mem_iSup_ker_pow g g' φ (fun v => LinearMap.congr_fun hφ v) hx

end L2b

section L3

variable {F V₁ V₀ : Type*} [Field F] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₀] [Module F V₀]

private theorem surjective_of_injective_of_adjoint [FiniteDimensional F V₀]
    (B₁ : LinearMap.BilinForm F V₁) (B₀ : LinearMap.BilinForm F V₀)
    (hB₁ : ∀ y, (∀ x, B₁ x y = 0) → y = 0)
    (α : V₀ →ₗ[F] V₁) (β : V₁ →ₗ[F] V₀) (hadj : ∀ x y, B₀ (β x) y = B₁ x (α y))
    (hα : Function.Injective α) : Function.Surjective β := by

  let ψ : V₀ →ₗ[F] Module.Dual F (LinearMap.range β) :=
    { toFun := fun y => (B₀.flip y).comp (LinearMap.range β).subtype
      map_add' := fun y y' => by ext; simp
      map_smul' := fun c y => by ext; simp }

  have hker : LinearMap.ker ψ = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    have hy' : ∀ x, B₀ (β x) y = 0 := fun x => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨β x, LinearMap.mem_range_self β x⟩
      simpa [ψ] using this
    apply hα
    rw [map_zero]
    exact hB₁ (α y) fun x => (hadj x y).symm.trans (hy' x)

  have hinj : Function.Injective ψ := LinearMap.ker_eq_bot.mp hker
  have h1 : Module.finrank F V₀ ≤ Module.finrank F (Module.Dual F (LinearMap.range β)) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Subspace.dual_finrank_eq] at h1
  have htop : LinearMap.range β = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h1)
  exact LinearMap.range_eq_top.mp htop

end L3

section L5

private theorem moduleFinite_zmod_of_int (p : ℕ) (Q : Type*) [AddCommGroup Q] [Module (ZMod p) Q]
    [Module.Finite ℤ Q] : Module.Finite (ZMod p) Q :=
  Module.Finite.of_restrictScalars_finite ℤ (ZMod p) Q

private scoped instance moduleFinite_int_quotPTop (p : ℕ) (V : Type*) [AddCommGroup V] [Module.Finite ℤ V] :
    Module.Finite ℤ (QuotPTop (V := V) p) :=
  Module.Finite.of_surjective (QuotientAddGroup.mk' (intPTop (V := V) p)).toIntLinearMap
    (QuotientAddGroup.mk'_surjective _)

private scoped instance moduleFinite_zmod_quotPTop (p : ℕ) (V : Type*) [AddCommGroup V] [Module.Finite ℤ V] :
    Module.Finite (ZMod p) (QuotPTop (V := V) p) :=
  moduleFinite_zmod_of_int p _

attribute [scoped instance] LevelRaising.moduleFinite_parabolicHoms_int

end L5

section L6

variable {F : Type*} [CommRing F]
variable {V V' V₁ : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
  [AddCommGroup V₁] [Module F V₁]

private def sumPairing (B : LinearMap.BilinForm F V) (B' : LinearMap.BilinForm F V') :
    LinearMap.BilinForm F (V × V') :=
  (B.comp (LinearMap.fst F V V') (LinearMap.fst F V V')) +
    (B'.comp (LinearMap.snd F V V') (LinearMap.snd F V V'))

@[scoped simp]
private theorem sumPairing_apply (B : LinearMap.BilinForm F V) (B' : LinearMap.BilinForm F V')
    (x y : V × V') : sumPairing B B' x y = B x.1 y.1 + B' x.2 y.2 := rfl

private theorem sumPairing_prod_coprod_adj (B₀ : LinearMap.BilinForm F V) (B₀' : LinearMap.BilinForm F V')
    (B₁ : LinearMap.BilinForm F V₁)
    (α₁ : V →ₗ[F] V₁) (α₂ : V' →ₗ[F] V₁) (β₁ : V₁ →ₗ[F] V) (β₂ : V₁ →ₗ[F] V')
    (h₁ : ∀ x y, B₀ (β₁ x) y = B₁ x (α₁ y)) (h₂ : ∀ x y', B₀' (β₂ x) y' = B₁ x (α₂ y')) :
    ∀ (x : V₁) (y : V × V'),
      sumPairing B₀ B₀' ((β₁.prod β₂) x) y = B₁ x ((α₁.coprod α₂) y) := by
  rintro x ⟨y, y'⟩
  simp [h₁, h₂, map_add]

end L6

section L8

open Polynomial

section field
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem exists_aeval_mem_iSup_ker_pow (g : Module.End F V) :
    ∃ q : F[X], q.eval 0 ≠ 0 ∧ ∀ v : V, aeval g q v ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n) := by
  obtain ⟨q, hq, hndvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd g.charpoly (LinearMap.charpoly_monic g).ne_zero 0
  refine ⟨q, ?_, fun v => ?_⟩
  · rwa [Ne, ← coeff_zero_eq_eval_zero, ← X_dvd_iff, ← sub_zero X, ← C_0]
  · have hCH : aeval g ((X - C 0) ^ g.charpoly.rootMultiplicity 0 * q) = 0 := by
      rw [← hq]; exact LinearMap.aeval_self_charpoly g
    have hv : (g ^ g.charpoly.rootMultiplicity 0) (aeval g q v) = 0 := by
      have := LinearMap.congr_fun hCH v
      simp only [map_mul, map_pow, aeval_X, map_zero, sub_zero, Module.End.mul_apply,
        LinearMap.zero_apply] at this
      exact this
    exact Submodule.mem_iSup_of_mem _ (LinearMap.mem_ker.mpr hv)

end field

private theorem exists_int_lift (p : ℕ) (q : (ZMod p)[X]) (a : ℤ) :
    ∃ s : ℤ[X], s.map (Int.castRingHom (ZMod p)) = q ∧
      ((s.eval a : ℤ) : ZMod p) = q.eval (a : ZMod p) := by
  obtain ⟨s, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) q
  exact ⟨s, rfl, by rw [eval_intCast_map]; rfl⟩

end L8

section L8b

open Polynomial

variable {V : Type*} [AddCommGroup V] (p : ℕ)

private theorem reductionModEnd_pow_mk (T : V →ₗ[ℤ] V) (n : ℕ) (v : V) :
    ((reductionModEnd p T) ^ n) (QuotientAddGroup.mk v : QuotPTop (V := V) p)
      = QuotientAddGroup.mk ((T ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, reductionModEnd_mk, ih]

private theorem mk_aeval_eq_aeval_reductionModEnd (T : V →ₗ[ℤ] V) (s : ℤ[X]) (v : V) :
    (QuotientAddGroup.mk (aeval T s v) : QuotPTop (V := V) p)
      = aeval (reductionModEnd p T) (s.map (Int.castRingHom (ZMod p))) (QuotientAddGroup.mk v) := by
  induction s using Polynomial.induction_on' generalizing v with
  | add f g hf hg =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, QuotientAddGroup.mk_add, hf, hg]
  | monomial n c =>
    simp only [Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.End.intCast_apply, reductionModEnd_pow_mk, eq_intCast,
      Int.cast_smul_eq_zsmul, QuotientAddGroup.mk_zsmul]

end L8b

section Assembly

private theorem prodMap_pow_apply {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] M) (n : ℕ) (x y : M) :
    ((LinearMap.prodMap f f) ^ n) (x, y) = ((f ^ n) x, (f ^ n) y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    exact ih (f x) (f y)

private theorem aeval_prodMap_apply {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] M) (s : Polynomial ℤ) (x y : M) :
    (Polynomial.aeval (LinearMap.prodMap f f) s) (x, y)
      = ((Polynomial.aeval f s) x, (Polynomial.aeval f s) y) := by
  induction s using Polynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, Prod.mk_add_mk]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
      prodMap_pow_apply, Algebra.algebraMap_eq_smul_one]
    rfl

private noncomputable def famPack {X : Type*} [Zero X] (τ : X) (U : ℕ → X) (S' : ℕ → Prop) (ℓ : ℕ) : X :=
  if ℓ = 1 then τ else @ite X (2 ≤ ℓ ∧ S' (ℓ - 2)) (Classical.propDecidable _) (U (ℓ - 2)) 0

private theorem famPack_one {X : Type*} [Zero X] (τ : X) (U : ℕ → X) (S' : ℕ → Prop) :
    famPack τ U S' 1 = τ := by
  simp [famPack]

private theorem famPack_of_two_le {X : Type*} [Zero X] (τ : X) (U : ℕ → X) (S' : ℕ → Prop) {ℓ : ℕ}
    (h2 : 2 ≤ ℓ) (hS : S' (ℓ - 2)) : famPack τ U S' ℓ = U (ℓ - 2) := by
  unfold famPack
  have h1 : ¬ ℓ = 1 := by omega
  rw [if_neg h1, if_pos (And.intro h2 hS)]

private theorem famPack_add_two {X : Type*} [Zero X] (τ : X) (U : ℕ → X) (S' : ℕ → Prop) (i : ℕ)
    (hi : S' i) : famPack τ U S' (i + 2) = U i := by
  rw [famPack_of_two_le τ U S' (Nat.le_add_left 2 i) (by rw [Nat.add_sub_cancel]; exact hi),
    Nat.add_sub_cancel]

private theorem famPack_of_not {X : Type*} [Zero X] (τ : X) (U : ℕ → X) (S' : ℕ → Prop) {ℓ : ℕ}
    (h1 : ¬ ℓ = 1) (h : ¬ (2 ≤ ℓ ∧ S' (ℓ - 2))) : famPack τ U S' ℓ = 0 := by
  unfold famPack
  rw [if_neg h1, if_neg h]

private theorem famPack_apply_mem {A : Type*} [AddZeroClass A] (par : Submodule ℤ (A →+ ℤ))
    (τ : (A →+ ℤ) →+ (A →+ ℤ)) (U : ℕ → ((A →+ ℤ) →+ (A →+ ℤ))) (S' : ℕ → Prop)
    (hτ : ∀ x ∈ par, τ x ∈ par) (hU : ∀ i, S' i → ∀ x ∈ par, U i x ∈ par)
    (ℓ : ℕ) (x : A →+ ℤ) (hx : x ∈ par) : famPack τ U S' ℓ x ∈ par := by
  by_cases h1 : ℓ = 1
  · rw [h1, famPack_one]
    exact hτ x hx
  · by_cases h2 : 2 ≤ ℓ ∧ S' (ℓ - 2)
    · rw [famPack_of_two_le τ U S' h2.1 h2.2]
      exact hU _ h2.2 x hx
    · rw [famPack_of_not τ U S' h1 h2]
      exact par.zero_mem

set_option maxHeartbeats 12800000 in

private theorem alpha_inj_aux {N q' : ℕ} [NeZero (N * q')] (p : ℕ) [Fact p.Prime]
    (τN : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ))
    (τM : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (hτNpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      τN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hτMpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      τM x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (res₀ res₁ : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (hrespar₀ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hrespar₁ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₁ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (e : ℤ)
    (hkill : ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, res₀ φ + res₁ ψ = (p : ℤ) • χ) →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ, τN φ - e • φ = (p : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ, τN ψ - e • ψ = (p : ℤ) • ψ'))
    (hresK₀ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)))
    (hresK₁ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)))
    (hkillK₀ : ∀ x : QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p,
        x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
        (reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) x = (e : ZMod p) • x →
        x = 0) :
    Function.Injective (LinearMap.coprod
      ((reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))).restrict hresK₀)
      ((reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))).restrict hresK₁)) := by
    intro a b hab
    have hab0 : (LinearMap.coprod
        ((reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))).restrict hresK₀)
        ((reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))).restrict hresK₁))
        (a - b) = 0 := by
      rw [map_sub, hab, sub_self]

    obtain ⟨φt, hφt⟩ := QuotientAddGroup.mk_surjective (a - b).1.1
    obtain ⟨ψt, hψt⟩ := QuotientAddGroup.mk_surjective (a - b).2.1

    have hjoint : ∃ χ : Additive (Gamma0 (N * q')) →+ ℤ,
        res₀ φt.1 + res₁ ψt.1 = (p : ℤ) • χ := by
      have h0 : (reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))) (a - b).1.1
          + (reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))) (a - b).2.1 = 0 := by
        have hv := congrArg Subtype.val hab0
        simpa [LinearMap.coprod_apply, LinearMap.restrict_apply] using hv
      rw [← hφt, ← hψt] at h0
      have h0' : (QuotientAddGroup.mk
            ((res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx)) φt
              + (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx)) ψt) :
          QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ) p) = 0 := by
        simpa using h0
      rw [QuotientAddGroup.eq_zero_iff] at h0'
      obtain ⟨w, hw⟩ := (mem_intPTop_iff p).mp h0'
      refine ⟨w.1, ?_⟩
      have hv := congrArg Subtype.val hw
      simpa [LinearMap.restrict_apply] using hv
    obtain ⟨hφEis, hψEis⟩ := hkill φt.1 ψt.1 φt.2 ψt.2 hjoint

    have hdesc : ∀ (φs : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
        (∃ φ' : Additive (Gamma0 N) →+ ℤ,
          τN φs.1 - e • φs.1 = (p : ℤ) • φ') →
        (reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) (QuotientAddGroup.mk φs)
          = (e : ZMod p) • (QuotientAddGroup.mk φs : QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p) := by
      intro φs hEis
      obtain ⟨φ', hφ'⟩ := hEis

      have hmem : φ' ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ := by
        refine parabolicHoms_int_saturated
          (Γ := Gamma0 N) (p := (p : ℤ)) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) φ' ?_
        rw [← hφ']
        exact sub_mem (hτNpar φs.1 φs.2)
          (Submodule.smul_mem _ _ φs.2)

      have hEis' : (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) φs
          - e • φs = (p : ℤ) • (⟨φ', hmem⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) := by
        apply Subtype.ext
        simpa [LinearMap.restrict_apply] using hφ'

      have hmk0 : (QuotientAddGroup.mk
            ((τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) φs
              - e • φs) :
          QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p) = 0 := by
        rw [QuotientAddGroup.eq_zero_iff]
        exact (mem_intPTop_iff p).mpr ⟨_, hEis'⟩
      have hsplit : (QuotientAddGroup.mk ((τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) φs) :
          QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p)
          = QuotientAddGroup.mk (e • φs) := by
        have hms : (QuotientAddGroup.mk ((τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) φs) :
            QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p)
            - QuotientAddGroup.mk (e • φs) = 0 := by
          rw [← QuotientAddGroup.mk_sub]
          exact hmk0
        exact sub_eq_zero.mp hms
      rw [reductionModHom_mk, hsplit, Int.cast_smul_eq_zsmul, QuotientAddGroup.mk_zsmul]

    have h1 : (a - b).1 = 0 := by
      apply Subtype.ext
      rw [← hφt]
      have := hdesc φt hφEis
      exact hkillK₀ _ (by rw [hφt]; exact (a - b).1.2) (by rw [hφt] at this ⊢; exact this)
    have h2 : (a - b).2 = 0 := by
      apply Subtype.ext
      rw [← hψt]
      have := hdesc ψt hψEis
      exact hkillK₀ _ (by rw [hψt]; exact (a - b).2.2) (by rw [hψt] at this ⊢; exact this)
    have hz : a - b = 0 := Prod.ext_iff.mpr ⟨h1, h2⟩
    exact sub_eq_zero.mp hz

set_option maxHeartbeats 12800000 in

private theorem beta_surj_aux {N q' : ℕ} [NeZero (N * q')] (p : ℕ) [Fact p.Prime]
    (τN : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ))
    (τM : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (hτNpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      τN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hτMpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      τM x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ]
      ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ] ℤ)
    (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
      ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ)
    (res₀ res₁ : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (β₀ β₁ : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ))
    (hrespar₀ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hrespar₁ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₁ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hβpar₀ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      β₀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβpar₁ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      β₁ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hproj₀ : ∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
      (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
        pair₀ ⟨β₀ x, hβpar₀ x x.2⟩ y = pair₁ x ⟨res₀ y, hrespar₀ y y.2⟩)
    (hproj₁ : ∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
      (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
        pair₀ ⟨β₁ x, hβpar₁ x x.2⟩ y = pair₁ x ⟨res₁ y, hrespar₁ y y.2⟩)
    (hresK₀ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)))
    (hresK₁ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)))
    (hβK₀ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) →
      (reductionModHom p (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)))
    (hβK₁ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) →
      (reductionModHom p (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)))
    (hαinj : Function.Injective (LinearMap.coprod
      ((reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))).restrict hresK₀)
      ((reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))).restrict hresK₁)))
    (hK₁right : ∀ y : ↥(⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)),
      (∀ x, (reductionMod p pair₁).restrict
          (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) x y = 0) → y = 0) :
    Function.Surjective (LinearMap.prod
      ((reductionModHom p (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))).restrict hβK₀)
      ((reductionModHom p (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))).restrict hβK₁)) := by
  haveI : NeZero N := ⟨fun hN => NeZero.ne (N * q') (by rw [hN, zero_mul])⟩

  have hpb₀ := reductionMod_adj_of_adj (p := p)
    (B := pair₁) (B₀ := pair₀)
    (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))
    (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
    (fun x y => hproj₀ x y)
  have hpb₁ := reductionMod_adj_of_adj (p := p)
    (B := pair₁) (B₀ := pair₀)
    (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))
    (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))
    (fun x y => hproj₁ x y)

  exact surjective_of_injective_of_adjoint
    ((reductionMod p pair₁).restrict _)
    (sumPairing
      ((reductionMod p pair₀).restrict _)
      ((reductionMod p pair₀).restrict _))
    hK₁right
    (LinearMap.coprod
      ((reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))).restrict hresK₀)
      ((reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))).restrict hresK₁))
    (LinearMap.prod
      ((reductionModHom p (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))).restrict hβK₀)
      ((reductionModHom p (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))).restrict hβK₁))
    (sumPairing_prod_coprod_adj _ _ _ _ _ _ _
      (fun x y => hpb₀ x.1 y.1) (fun x y => hpb₁ x.1 y.1))
    hαinj

set_option maxHeartbeats 12800000 in
private theorem assemble
    {N q' : ℕ} [NeZero (N * q')] [NeZero q']
    (p : ℕ) [Fact p.Prime]

    (τN : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ))
    (τM : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (hτNpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      τN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hτMpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      τM x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)

    (UN : ℕ → ((Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ)))
    (UM : ℕ → ((Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ)))
    (S' : ℕ → Prop)
    (hUMpar : ∀ i, S' i → ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      UM i x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hUcomm : ∀ i, S' i → ∀ x, UM i (τM x) = τM (UM i x))

    (φ₀ : Additive (Gamma0 N) →+ ℤ)
    (hφ₀par : φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hφ₀ne : (Int.castAddHom (ZMod p)).comp φ₀ ≠ 0)
    (hφ₀τ : ∃ ψ : Additive (Gamma0 N) →+ ℤ, τN φ₀ = (p : ℤ) • ψ)
    (hφ₀U : ∀ i, S' i → ∃ ψ : Additive (Gamma0 N) →+ ℤ, UN i φ₀ = (p : ℤ) • ψ)
    (c : ℤ) (hc : (p : ℤ) ∣ c ^ 2 - ((q' : ℤ) + 1) ^ 2)
    (hφ₀q' : ∃ ψ : Additive (Gamma0 N) →+ ℤ, HeckeEis.heckeOperatorHom N q' ℤ φ₀ - c • φ₀ = (p : ℤ) • ψ)

    (res₀ res₁ : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ))
    (hrespar₀ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hrespar₁ : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      res₁ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hresτ₀ : ∀ φ, res₀ (τN φ) = τM (res₀ φ))
    (hresτ₁ : ∀ φ, res₁ (τN φ) = τM (res₁ φ))
    (hresU₀ : ∀ i, S' i → ∀ φ, res₀ (UN i φ) = UM i (res₀ φ))
    (hresU₁ : ∀ i, S' i → ∀ φ, res₁ (UN i φ) = UM i (res₁ φ))

    (β₀ β₁ : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ))
    (hβpar₀ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      β₀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβpar₁ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      β₁ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβτ₀ : ∀ x, β₀ (τM x) = τN (β₀ x))
    (hβτ₁ : ∀ x, β₁ (τM x) = τN (β₁ x))
    (hentry₀₀ : ∀ y, β₀ (res₀ y) = ((q' : ℤ) + 1) • y)
    (hentry₁₁ : ∀ y, β₁ (res₁ y) = ((q' : ℤ) + 1) • y)
    (hentry₀₁ : ∀ y, β₀ (res₁ y) = HeckeEis.heckeOperatorHom N q' ℤ y)
    (hentry₁₀ : ∀ y, β₁ (res₀ y) = HeckeEis.heckeOperatorHom N q' ℤ y)

    (e : ℤ) (he : (e : ZMod p) ≠ 0)
    (hkill : ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, res₀ φ + res₁ ψ = (p : ℤ) • χ) →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ, τN φ - e • φ = (p : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ, τN ψ - e • ψ = (p : ℤ) • ψ'))

    (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ]
      ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ] ℤ)
    (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
      ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ)
    (hperf₁ : (∀ x, (∀ y, (p : ℤ) ∣ pair₁ x y) → ∃ x', x = (p : ℤ) • x') ∧
      (∀ y, (∀ x, (p : ℤ) ∣ pair₁ x y) → ∃ y', y = (p : ℤ) • y'))
    (hperf₀ : (∀ x, (∀ y, (p : ℤ) ∣ pair₀ x y) → ∃ x', x = (p : ℤ) • x') ∧
      (∀ y, (∀ x, (p : ℤ) ∣ pair₀ x y) → ∃ y', y = (p : ℤ) • y'))
    (hadjτ₁ : ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      pair₁ ⟨τM x, hτMpar x x.2⟩ y = pair₁ x ⟨τM y, hτMpar y y.2⟩)
    (hadjτ₀ : ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      pair₀ ⟨τN x, hτNpar x x.2⟩ y = pair₀ x ⟨τN y, hτNpar y y.2⟩)
    (hproj₀ : ∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
      (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
        pair₀ ⟨β₀ x, hβpar₀ x x.2⟩ y = pair₁ x ⟨res₀ y, hrespar₀ y y.2⟩)
    (hproj₁ : ∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
      (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
        pair₀ ⟨β₁ x, hβpar₁ x x.2⟩ y = pair₁ x ⟨res₁ y, hrespar₁ y y.2⟩) :
    ∃ H : Additive (Gamma0 (N * q')) →+ ℤ,
      H ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ ∧ β₀ H = 0 ∧ β₁ H = 0 ∧
      (Int.castAddHom (ZMod p)).comp H ≠ 0 ∧
      ∀ i, S' i → ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ, UM i H = (p : ℤ) • ψ := by
  haveI : NeZero N := ⟨fun hN => NeZero.ne (N * q') (by rw [hN, zero_mul])⟩
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have _ := hperf₀
  have _ := hadjτ₀

  have hBl₁ := (separatingLeft_reductionMod_iff p pair₁).mpr hperf₁.1
  have hBr₁ := (separatingRight_reductionMod_iff p pair₁).mpr hperf₁.2

  have hT₁adj : ∀ x y,
      reductionMod p pair₁
          (reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)) x) y
        = reductionMod p pair₁ x
          (reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)) y) :=
    reductionMod_reductionModHom_selfAdjoint p pair₁ _
      (fun x y => by exact hadjτ₁ x y)

  haveI hfd₁ : Module.Finite (ZMod p)
      (QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ) p) :=
    inferInstance
  haveI hfd₀ : Module.Finite (ZMod p)
      (QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p) :=
    inferInstance

  have hK₁nd := restrict_iSup_ker_pow_nondegenerate
    (reductionMod p pair₁) hBl₁ hBr₁
    (reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)))
    hT₁adj

  have hresT₀ :
      (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx)) ∘ₗ
        (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
      = (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)) ∘ₗ
        (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hresτ₀ x.1
  have hresT₁ :
      (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx)) ∘ₗ
        (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
      = (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)) ∘ₗ
        (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hresτ₁ x.1
  have hβT₀ :
      (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx)) ∘ₗ
        (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
      = (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) ∘ₗ
        (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hβτ₀ x.1
  have hβT₁ :
      (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)) ∘ₗ
        (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
      = (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) ∘ₗ
        (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hβτ₁ x.1

  obtain ⟨ψq', hψq'⟩ := hφ₀q'
  obtain ⟨ψτ, hψτ⟩ := hφ₀τ

  have hkill1 : ∀ w : ℤ,
      (∃ δ : Additive (Gamma0 N) →+ ℤ,
        τN (w • φ₀) - e • (w • φ₀) = (p : ℤ) • δ) →
      (w : ZMod p) = 0 := by
    intro w hEis
    obtain ⟨δ, hδ⟩ := hEis
    have hTw : τN (w • φ₀) = (p : ℤ) • (w • ψτ) := by
      rw [map_zsmul, hψτ, smul_comm w (p : ℤ) ψτ]
    have hcomb : e • (w • φ₀) = (p : ℤ) • (w • ψτ - δ) := by
      rw [smul_sub, ← hTw, ← hδ]
      abel
    by_contra hw
    apply hφ₀ne
    ext γ
    show ((φ₀ γ : ℤ) : ZMod p) = 0
    have hγ := congrArg (fun f : Additive (Gamma0 N) →+ ℤ => f γ) hcomb
    simp only [AddMonoidHom.smul_apply, zsmul_eq_mul, Int.cast_id] at hγ
    have hz : ((e * (w * φ₀ γ) : ℤ) : ZMod p) = 0 := by
      rw [hγ]
      push_cast
      simp
    push_cast at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h he
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hw
    · exact h'

  have hgUuv : ∀ (u v : ℤ) (i : ℕ), S' i → ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      UM i (u • res₀ φ₀ + v • res₁ φ₀) = (p : ℤ) • ψ := by
    intro u v i hi
    obtain ⟨ψi, hψi⟩ := hφ₀U i hi
    refine ⟨u • res₀ ψi + v • res₁ ψi, ?_⟩
    calc UM i (u • res₀ φ₀ + v • res₁ φ₀)
        = u • UM i (res₀ φ₀) + v • UM i (res₁ φ₀) := by
          rw [map_add, map_zsmul, map_zsmul]
      _ = u • res₀ (UN i φ₀) + v • res₁ (UN i φ₀) := by
          rw [← hresU₀ i hi φ₀, ← hresU₁ i hi φ₀]
      _ = (p : ℤ) • (u • res₀ ψi + v • res₁ ψi) := by
          rw [hψi, map_zsmul, map_zsmul, smul_comm u (p : ℤ), smul_comm v (p : ℤ),
            ← smul_add]
  have hgτuv : ∀ (u v : ℤ), ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      τM (u • res₀ φ₀ + v • res₁ φ₀) = (p : ℤ) • ψ := by
    intro u v
    refine ⟨u • res₀ ψτ + v • res₁ ψτ, ?_⟩
    calc τM (u • res₀ φ₀ + v • res₁ φ₀)
        = u • τM (res₀ φ₀) + v • τM (res₁ φ₀) := by
          rw [map_add, map_zsmul, map_zsmul]
      _ = u • res₀ (τN φ₀) + v • res₁ (τN φ₀) := by
          rw [← hresτ₀ φ₀, ← hresτ₁ φ₀]
      _ = (p : ℤ) • (u • res₀ ψτ + v • res₁ ψτ) := by
          rw [hψτ, map_zsmul, map_zsmul, smul_comm u (p : ℤ), smul_comm v (p : ℤ),
            ← smul_add]

  have hT : HeckeEis.heckeOperatorHom N q' ℤ φ₀ = c • φ₀ + (p : ℤ) • ψq' := by
    rw [← hψq']; abel

  have hparuv : ∀ u v : ℤ, (u • res₀ φ₀ + v • res₁ φ₀)
      ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ := fun u v =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hrespar₀ φ₀ hφ₀par))
      (Submodule.smul_mem _ _ (hrespar₁ φ₀ hφ₀par))

  obtain ⟨g, hgpar, hgne, hgβ₀, hgβ₁, hgτ, hgU⟩ :
      ∃ g : Additive (Gamma0 (N * q')) →+ ℤ,
        g ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ ∧
        (Int.castAddHom (ZMod p)).comp g ≠ 0 ∧
        (∃ δ₀, β₀ g = (p : ℤ) • δ₀) ∧
        (∃ δ₁, β₁ g = (p : ℤ) • δ₁) ∧
        (∃ ψ, τM g = (p : ℤ) • ψ) ∧
        (∀ i, S' i → ∃ ψ, UM i g = (p : ℤ) • ψ) := by
    by_cases hdeg : ((c : ZMod p) = 0 ∧ ((q' : ZMod p) + 1) = 0)
    ·
      obtain ⟨hdc, hdq⟩ := hdeg
      obtain ⟨kc, hkc⟩ : (p : ℤ) ∣ c := by
        rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨kq, hkq⟩ : (p : ℤ) ∣ ((q' : ℤ) + 1) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact hdq
      refine ⟨(1 : ℤ) • res₀ φ₀ + (0 : ℤ) • res₁ φ₀, hparuv 1 0, ?_, ⟨kq • φ₀, ?_⟩,
        ⟨kc • φ₀ + ψq', ?_⟩, hgτuv 1 0, fun i hi => hgUuv 1 0 i hi⟩
      ·
        intro h0
        obtain ⟨x', hx'⟩ := (LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff
            (p := p) ⟨(1 : ℤ) • res₀ φ₀ + (0 : ℤ) • res₁ φ₀, hparuv 1 0⟩).mp
          (AddMonoidHom.ext fun γ => congrArg (fun f => f γ) h0)
        have hpre : ∃ χ' : Additive (Gamma0 (N * q')) →+ ℤ,
            res₀ ((1 : ℤ) • φ₀) + res₁ ((0 : ℤ) • φ₀) = (p : ℤ) • χ' := by
          refine ⟨(x' : Additive (Gamma0 (N * q')) →+ ℤ), ?_⟩
          rw [map_zsmul, map_zsmul]
          simpa using congrArg Subtype.val hx'
        obtain ⟨hEA, _⟩ := hkill ((1 : ℤ) • φ₀) ((0 : ℤ) • φ₀) (Submodule.smul_mem _ (1 : ℤ) hφ₀par)
          (Submodule.smul_mem _ (0 : ℤ) hφ₀par) hpre
        have h1 : (((1 : ℤ) : ZMod p)) = 0 := hkill1 1 hEA
        rw [Int.cast_one] at h1
        exact one_ne_zero h1
      ·
        rw [map_add, map_zsmul, map_zsmul, hentry₀₀, hentry₀₁, hT, hkq]
        module
      ·
        rw [map_add, map_zsmul, map_zsmul, hentry₁₀, hentry₁₁, hT, hkc]
        module
    ·
      obtain ⟨k, hk⟩ := hc
      refine ⟨(-c) • res₀ φ₀ + ((q' : ℤ) + 1) • res₁ φ₀, hparuv (-c) ((q' : ℤ) + 1), ?_,
        ⟨((q' : ℤ) + 1) • ψq', ?_⟩, ⟨(-k) • φ₀ - c • ψq', ?_⟩,
        hgτuv (-c) ((q' : ℤ) + 1), fun i hi => hgUuv (-c) ((q' : ℤ) + 1) i hi⟩
      ·
        intro h0
        obtain ⟨x', hx'⟩ := (LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff
            (p := p) ⟨(-c) • res₀ φ₀ + ((q' : ℤ) + 1) • res₁ φ₀,
              hparuv (-c) ((q' : ℤ) + 1)⟩).mp
          (AddMonoidHom.ext fun γ => congrArg (fun f => f γ) h0)
        have hpre : ∃ χ' : Additive (Gamma0 (N * q')) →+ ℤ,
            res₀ ((-c) • φ₀) + res₁ (((q' : ℤ) + 1) • φ₀) = (p : ℤ) • χ' := by
          refine ⟨(x' : Additive (Gamma0 (N * q')) →+ ℤ), ?_⟩
          rw [map_zsmul, map_zsmul]
          simpa using congrArg Subtype.val hx'
        obtain ⟨hEA, hEB⟩ := hkill ((-c) • φ₀) (((q' : ℤ) + 1) • φ₀) (Submodule.smul_mem _ (-c) hφ₀par)
          (Submodule.smul_mem _ ((q' : ℤ) + 1) hφ₀par) hpre
        have hc0 : ((-c : ℤ) : ZMod p) = 0 := hkill1 (-c) hEA
        have hq0 : ((((q' : ℤ) + 1) : ℤ) : ZMod p) = 0 := hkill1 _ hEB
        apply hdeg
        refine ⟨?_, ?_⟩
        · rw [Int.cast_neg, neg_eq_zero] at hc0
          exact hc0
        · push_cast at hq0
          exact hq0
      ·
        rw [map_add, map_zsmul, map_zsmul, hentry₀₀, hentry₀₁, hT]
        module
      ·
        rw [map_add, map_zsmul, map_zsmul, hentry₁₀, hentry₁₁, hT]
        match_scalars
        · linarith [hk]
        · ring

  have hresbarT₀ := reductionModHom_comp_of_comp (p := p)
    (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))
    (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
    (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
    hresT₀
  have hresbarT₁ := reductionModHom_comp_of_comp (p := p)
    (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))
    (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
    (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
    hresT₁
  have hβbarT₀ := reductionModHom_comp_of_comp (p := p)
    (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
    (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
    (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
    hβT₀
  have hβbarT₁ := reductionModHom_comp_of_comp (p := p)
    (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))
    (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
    (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
    hβT₁

  have hresK₀ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₀.toIntLinearMap.restrict (fun x hx => hrespar₀ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) :=
    fun x hx => map_mem_iSup_ker_pow' _ _ _ hresbarT₀ hx
  have hresK₁ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModHom p (res₁.toIntLinearMap.restrict (fun x hx => hrespar₁ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) :=
    fun x hx => map_mem_iSup_ker_pow' _ _ _ hresbarT₁ hx
  have hβK₀ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) →
      (reductionModHom p (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) :=
    fun x hx => map_mem_iSup_ker_pow' _ _ _ hβbarT₀ hx
  have hβK₁ : ∀ x, x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))) ^ n)) →
      (reductionModHom p (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) x ∈
      (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) :=
    fun x hx => map_mem_iSup_ker_pow' _ _ _ hβbarT₁ hx

  have hkillK₀ : ∀ x : QuotPTop (V := ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) p,
      x ∈ (⨆ n : ℕ, LinearMap.ker ((reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ^ n)) →
      (reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) x = (e : ZMod p) • x →
      x = 0 :=
    fun x hxK hxeig => eq_zero_of_mem_iSup_ker_pow_of_apply_eq_smul _ he hxK hxeig

  have hαinj := alpha_inj_aux p τN τM hτNpar hτMpar res₀ res₁ hrespar₀ hrespar₁ e hkill
    hresK₀ hresK₁ hkillK₀
  have hβsurj := beta_surj_aux p τN τM hτNpar hτMpar pair₁ pair₀ res₀ res₁ β₀ β₁ hrespar₀ hrespar₁
    hβpar₀ hβpar₁ hproj₀ hproj₁ hresK₀ hresK₁ hβK₀ hβK₁ hαinj hK₁nd.2

  have hβpairT :
      (LinearMap.prod
          (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
          (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) ∘ₗ
        (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx))
      = (LinearMap.prodMap
          (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
          (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ∘ₗ
        (LinearMap.prod
          (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
          (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) := by
    refine LinearMap.ext fun x => Prod.ext ?_ ?_
    · exact LinearMap.congr_fun hβT₀ x
    · exact LinearMap.congr_fun hβT₁ x

  obtain ⟨q, hqunit, hqmem⟩ :=
    exists_aeval_mem_iSup_ker_pow
      (reductionModEnd p (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)))
  obtain ⟨s, hsmap, hseval⟩ := exists_int_lift p q 0
  have hsunit : ((s.eval 0 : ℤ) : ZMod p) ≠ 0 := by
    rw [hseval, Int.cast_zero]
    exact hqunit
  have hL4b := LevelRaising.exists_mem_range_of_forall_exists_add_dvd
    (τ₀ := LinearMap.prodMap
      (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
      (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)))
    (τ₁ := (τM.toIntLinearMap.restrict (fun x hx => hτMpar x hx)))
    (β := LinearMap.prod
      (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
      (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)))
    hβpairT (p := p) 0 (fun c => by
      obtain ⟨c₁, c₂⟩ := c
      refine ⟨s, hsunit, ?_⟩
      obtain ⟨k, hk⟩ := hβsurj
        (⟨QuotientAddGroup.mk ((Polynomial.aeval
            (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) s) c₁),
          by rw [mk_aeval_eq_aeval_reductionModEnd, hsmap]; exact hqmem _⟩,
         ⟨QuotientAddGroup.mk ((Polynomial.aeval
            (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) s) c₂),
          by rw [mk_aeval_eq_aeval_reductionModEnd, hsmap]; exact hqmem _⟩)
      obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective k.val
      have hk₁ := Subtype.ext_iff.mp (congrArg Prod.fst hk)
      have hk₂ := Subtype.ext_iff.mp (congrArg Prod.snd hk)
      simp only [LinearMap.prod_apply, Function.prod, LinearMap.coe_restrict_apply] at hk₁ hk₂
      rw [← hx, reductionModHom_mk] at hk₁ hk₂
      obtain ⟨w₁, hw₁⟩ := (mem_intPTop_iff (p := p)).mp
        ((QuotientAddGroup.eq).mp hk₁)
      obtain ⟨w₂, hw₂⟩ := (mem_intPTop_iff (p := p)).mp
        ((QuotientAddGroup.eq).mp hk₂)
      refine ⟨x, (w₁, w₂), ?_⟩
      rw [aeval_prodMap_apply]
      have h1 : (Polynomial.aeval (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) s) c₁
          = (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx)) x + (p : ℤ) • w₁ := by
        rw [← hw₁, add_neg_cancel_left]
      have h2 : (Polynomial.aeval (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) s) c₂
          = (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)) x + (p : ℤ) • w₂ := by
        rw [← hw₂, add_neg_cancel_left]
      exact Prod.ext h1 h2)

  have hT₁par' : ∀ (ℓ : ℕ) (x : Additive (Gamma0 (N * q')) →+ ℤ),
      x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →
      famPack τM UM S' ℓ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ :=
    fun ℓ x hx => famPack_apply_mem _ τM UM S' hτMpar hUMpar ℓ x hx
  have hβT₀' :
      (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx)) ∘ₗ
        ((famPack τM UM S' 1).toIntLinearMap.restrict (hT₁par' 1))
      = (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) ∘ₗ
        (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := hβτ₀ x.1
    rw [← famPack_one τM UM S'] at h
    exact h
  have hβT₁' :
      (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)) ∘ₗ
        ((famPack τM UM S' 1).toIntLinearMap.restrict (hT₁par' 1))
      = (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx)) ∘ₗ
        (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx)) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := hβτ₁ x.1
    rw [← famPack_one τM UM S'] at h
    exact h
  have hβpackT :
      (LinearMap.prod
          (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
          (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) ∘ₗ
        ((famPack τM UM S' 1).toIntLinearMap.restrict (hT₁par' 1))
      = (LinearMap.prodMap
          (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))
          (τN.toIntLinearMap.restrict (fun x hx => hτNpar x hx))) ∘ₗ
        (LinearMap.prod
          (β₀.toIntLinearMap.restrict (fun x hx => hβpar₀ x hx))
          (β₁.toIntLinearMap.restrict (fun x hx => hβpar₁ x hx))) := by
    refine LinearMap.ext fun x => Prod.ext ?_ ?_
    · exact LinearMap.congr_fun hβT₀' x
    · exact LinearMap.congr_fun hβT₁' x
  obtain ⟨H, hHpar, hH₀, hH₁, hHne, hHeig⟩ :=
    LevelRaising.exists_ker_pair_castAddHom_comp_ne_zero
      (ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
      (ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
      (p := p)
      (fun ℓ _ => famPack τM UM S' ℓ)
      (fun ℓ _ => hT₁par' ℓ)
      1 τN (fun x hx => hτNpar x hx)
      β₀ β₁ hβpar₀ hβpar₁ hβpackT
      (fun _ => (0 : ℤ))
      (fun ℓ => 2 ≤ ℓ ∧ S' (ℓ - 2))
      (fun ℓ _ hS x => by
        have h' : famPack τM UM S' ℓ (famPack τM UM S' 1 x)
            = famPack τM UM S' 1 (famPack τM UM S' ℓ x) := by
          rw [famPack_one, famPack_of_two_le τM UM S' hS.1 hS.2]
          exact hUcomm _ hS.2 x
        exact h')
      hL4b
      (fun δ hδ => parabolicHoms_int_saturated hpne δ hδ)
      g hgpar hgne hgβ₀ hgβ₁
      (by
        obtain ⟨ψ, hψ⟩ := hgτ
        have h' : famPack τM UM S' 1 g - (0 : ℤ) • g = (p : ℤ) • ψ := by
          rw [famPack_one, hψ]
          module
        exact ⟨ψ, h'⟩)
      (fun ℓ _ hS => by
        obtain ⟨ψ, hψ⟩ := hgU (ℓ - 2) hS.2
        have h' : famPack τM UM S' ℓ g - (0 : ℤ) • g = (p : ℤ) • ψ := by
          rw [famPack_of_two_le τM UM S' hS.1 hS.2, hψ]
          module
        exact ⟨ψ, h'⟩)

  refine ⟨H, hHpar, hH₀, hH₁, hHne, fun i hi => ?_⟩
  haveI : NeZero (i + 2) := ⟨by omega⟩
  have hS2 : 2 ≤ i + 2 ∧ S' (i + 2 - 2) := ⟨by omega, by rw [Nat.add_sub_cancel]; exact hi⟩
  obtain ⟨ψ, hψ⟩ := hHeig (i + 2) hS2
  have hψ' : famPack τM UM S' (i + 2) H - (0 : ℤ) • H = (p : ℤ) • ψ := hψ
  rw [famPack_add_two τM UM S' i hi] at hψ'
  exact ⟨ψ, by rw [← hψ']; module⟩

end Assembly

end LRf.Engine
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf"

end Engine
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

section Endgame
set_option autoImplicit false

open CongruenceSubgroup

namespace LRf

namespace Endgame

private theorem isMaximal_comap {N q' : ℕ} [NeZero (N * q')]
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal) : (Ideal.comap χ₁ 𝔪).IsMaximal := by
  haveI := h𝔪
  refine Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' χ₁ ?_ 𝔪
  refine RingHom.IsIntegral.tower_top
    (algebraMap ℤ (CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'})) χ₁ fun x => ?_
  obtain ⟨f, hf, hfx⟩ := integralClosure.isIntegral x
  refine ⟨f, hf, ?_⟩
  rwa [RingHom.ext_int (χ₁.comp (algebraMap ℤ (CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'})))
    (algebraMap ℤ (integralClosure ℤ ℂ))]

private theorem heckeWordHom_apply_eq_zero_of_wordValue_eq_zero
    {N q' : ℕ} [NeZero (N * q')] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (A : ModularForm.AtkinLehnerDatum (N * q') q') (P : FreeAlgebra ℤ ℕ) (hP : wordValue N q' P = 0)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (h₀ : HeckeEis.degeneracyTransfer₀ N q' ℤ hq' hq'N φ = 0) (h₁ : HeckeEis.degeneracyTransfer₁ N q' ℤ φ = 0) :
    HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} P φ = 0 :=
  CuspForm.heckeWordHom_eq_zero_of_forall_newLattice hq' hq'N A P
    (fun f _ =>
      (congrArg (fun t : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} =>
          (t : Module.End ℂ (CuspForm (Gamma0 (N * q')) 2)) f) hP).trans
        (LinearMap.zero_apply f))
    φ hφ h₀ h₁

private theorem exists_word_smul_of_mem_span {N q' : ℕ} [NeZero (N * q')] (p : ℕ)
    (r : ℕ) (ws : ℕ → FreeAlgebra ℤ ℕ) (H : Additive (Gamma0 (N * q')) →+ ℤ)
    (hHU : ∀ i, i < r → ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} (ws i) H = (p : ℤ) • ψ)
    {m : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}}
    (hm : m ∈ Ideal.span (Set.range fun i : Fin r => wordValue N q' (ws i))) :
    ∃ R : FreeAlgebra ℤ ℕ, wordValue N q' R = m ∧ ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} R H = (p : ℤ) • ψ := by
  rw [← Ideal.submodule_span_eq] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨ws i.1, rfl, hHU i.1 i.2⟩
  | zero =>
      exact ⟨0, map_zero (wordValue N q'), 0, by
        rw [map_zero (HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'}), LinearMap.zero_apply]
        exact (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
      obtain ⟨R₁, hR₁, ψ₁, hψ₁⟩ := hx
      obtain ⟨R₂, hR₂, ψ₂, hψ₂⟩ := hy
      exact ⟨R₁ + R₂, by rw [map_add, hR₁, hR₂], ψ₁ + ψ₂, by
        rw [map_add, LinearMap.add_apply, hψ₁, hψ₂]
        exact (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
      obtain ⟨R, hR, ψ, hψ⟩ := hx
      obtain ⟨Q, hQ⟩ := exists_wordValue_eq N q' a
      exact ⟨Q * R, by rw [map_mul, hQ, hR, smul_eq_mul], HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} Q ψ, by
        rw [map_mul, Module.End.mul_apply, hψ]
        exact map_zsmul _ _ _⟩

private theorem exists_words_span
    {N q' : ℕ} [NeZero (N * q')]
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) :
    ∃ (r : ℕ) (ws : ℕ → FreeAlgebra ℤ ℕ),
      (∀ i, i < r → χ₁ (wordValue N q' (ws i)) ∈ 𝔪) ∧
      Ideal.span (Set.range fun i : Fin r => wordValue N q' (ws i)) = Ideal.comap χ₁ 𝔪 := by
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}) :=
    CuspForm.moduleFinite_heckeAlgebra_two (N * q') {ℓ | ℓ ∣ N * q'}
  haveI : IsNoetherianRing (CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}) :=
    isNoetherian_of_tower ℤ inferInstance
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (Ideal.comap χ₁ 𝔪))
  choose P hP using fun i : Fin r => exists_wordValue_eq N q' (s i)
  refine ⟨r, fun i => if h : i < r then P ⟨i, h⟩ else 0, fun i hi => ?_, ?_⟩
  · have hmem : s ⟨i, hi⟩ ∈ Ideal.comap χ₁ 𝔪 := by
      rw [← hs]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    have hmem' : χ₁ (s ⟨i, hi⟩) ∈ 𝔪 := Ideal.mem_comap.mp hmem
    show χ₁ (wordValue N q' (if h : i < r then P ⟨i, h⟩ else 0)) ∈ 𝔪
    rw [dif_pos hi, hP]
    exact hmem'
  · have hfun : (fun i : Fin r => wordValue N q' (if h : (i : ℕ) < r then P ⟨i, h⟩ else 0)) = s := by
      funext i
      show wordValue N q' (if h : (i : ℕ) < r then P ⟨i, h⟩ else 0) = s i
      rw [dif_pos i.2]
      exact hP i
    show Ideal.span (Set.range fun i : Fin r =>
      wordValue N q' (if h : (i : ℕ) < r then P ⟨i, h⟩ else 0)) = _
    rw [hfun]
    exact hs

private theorem mem_comap_of_new_class
    {N q' : ℕ} [NeZero (N * q')] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (A : ModularForm.AtkinLehnerDatum (N * q') q')
    (p : ℕ) [Fact p.Prime]
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (r : ℕ) (ws : ℕ → FreeAlgebra ℤ ℕ)
    (hspan : Ideal.span (Set.range fun i : Fin r => wordValue N q' (ws i)) = Ideal.comap χ₁ 𝔪)
    (H : Additive (Gamma0 (N * q')) →+ ℤ)
    (hHpar : H ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
    (hH₀ : HeckeEis.degeneracyTransfer₀ N q' ℤ hq' hq'N H = 0)
    (hH₁ : HeckeEis.degeneracyTransfer₁ N q' ℤ H = 0)
    (hHne : (Int.castAddHom (ZMod p)).comp H ≠ 0)
    (hHU : ∀ i, i < r → ∃ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} (ws i) H = (p : ℤ) • ψ) :
    ∀ T : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'},
      (∀ g ∈ LinearMap.ker (CuspForm.traceLin A hq')
            ⊓ LinearMap.ker ((CuspForm.traceLin A hq') ∘ₗ (CuspForm.atkinLehnerLin A 2)),
        (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * q')) 2)) g = 0) →
      T ∈ Ideal.comap χ₁ 𝔪 := by
  intro T hT
  have hmax : (Ideal.comap χ₁ 𝔪).IsMaximal := isMaximal_comap χ₁ h𝔪
  have _ := hp𝔪
  by_contra hTI

  obtain ⟨u, m₁, hm₁, h1⟩ := hmax.exists_inv hTI
  obtain ⟨PT, hPT⟩ := exists_wordValue_eq N q' T
  obtain ⟨Q, hQ⟩ := exists_wordValue_eq N q' u

  obtain ⟨R₁, hR₁, ψ₁, hψ₁⟩ := exists_word_smul_of_mem_span p r ws H hHU (m := m₁) (by rw [hspan]; exact hm₁)

  have hPT0 : HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} PT H = 0 :=
    CuspForm.heckeWordHom_eq_zero_of_forall_newLattice hq' hq'N A PT
      (fun f hf =>
        (congrArg (fun t : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} =>
            (t : Module.End ℂ (CuspForm (Gamma0 (N * q')) 2)) f) hPT).trans
          (hT f ⟨(hf 1 (Subalgebra.one_mem _)).2.1, (hf 1 (Subalgebra.one_mem _)).2.2⟩))
      H hHpar hH₀ hH₁

  have hW : wordValue N q' (Q * PT + R₁ - 1) = 0 := by
    rw [map_sub, map_add, map_mul, map_one, hQ, hPT, hR₁, h1, sub_self]
  have hW0 := heckeWordHom_apply_eq_zero_of_wordValue_eq_zero hq' hq'N A (Q * PT + R₁ - 1) hW H hHpar hH₀ hH₁
  rw [map_sub, map_add, map_mul, map_one, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hPT0,
    map_zero, zero_add, Module.End.one_apply, hψ₁, sub_eq_zero] at hW0

  apply hHne
  refine AddMonoidHom.ext fun g => ?_
  have hg : ((p : ℤ) • ψ₁) g = (p : ℤ) * ψ₁ g := rfl
  show ((H g : ℤ) : ZMod p) = 0
  rw [← hW0, hg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

end Endgame
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

end LRf
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

end Endgame
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

section Assembly
set_option Elab.async false
set_option autoImplicit false

open CongruenceSubgroup HeckeEis

section EngineInline
open scoped MatrixGroups

namespace INHX2

section Generic
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

private theorem section_cocycle_mem (H : Subgroup G) (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q)
    (g : G) (q : G ⧸ H) : (R (g • q))⁻¹ * (g * R q) ∈ H := by
  refine QuotientGroup.eq.mp ?_
  rw [hR (g • q)]
  show g • q = ((g * R q : G) : G ⧸ H)
  rw [show ((g * R q : G) : G ⧸ H) = g • ((R q : G) : G ⧸ H) from rfl, hR q]

private theorem coresHom_apply_section (H : Subgroup G) [H.FiniteIndex] (φ : Additive ↥H →+ A)
    (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul
        (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hmem : ∀ q : G ⧸ H, (Quotient.out q)⁻¹ * R q ∈ H := fun q => by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq', hR q]
  have hsplit : ∀ q : G ⧸ H,
      φ (Additive.ofMul (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = φ (Additive.ofMul (transferAux H g q))
          + (φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H))
             - φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))) := by
    intro q
    have hdec : (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)
        = (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H)⁻¹
            * transferAux H g q * (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H) := by
      ext
      show (R (g • q))⁻¹ * (g * R q)
          = ((Quotient.out (g • q))⁻¹ * R (g • q))⁻¹
              * ((g • q).out⁻¹ * (g * Quotient.out q)) * ((Quotient.out q)⁻¹ * R q)
      group
    rw [hdec, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel
  have hre : ∑ q : G ⧸ H,
      φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H)) :=
    Fintype.sum_equiv
      (⟨fun q => g • q, fun q => g⁻¹ • q, fun q => inv_smul_smul g q,
        fun q => smul_inv_smul g q⟩ : (G ⧸ H) ≃ (G ⧸ H))
      _ _ (fun q => rfl)
  have hsec : ∑ q : G ⧸ H, φ (Additive.ofMul
      (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) := by
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hre]
    simp
  rw [coresHom_apply, hsec]

end Generic
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

section Transport
variable {K G' : Type*} [Group K] [Group G'] {A : Type*} [AddCommGroup A]

private def quotMap (H' : Subgroup G') (σ : K →* G') : K ⧸ (H'.comap σ) → G' ⧸ H' :=
  Quotient.map' σ (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [map_mul, map_inv] using hab)

@[scoped simp] private theorem quotMap_mk (H' : Subgroup G') (σ : K →* G') (k : K) :
    quotMap H' σ ((k : K ⧸ (H'.comap σ))) = ((σ k : G') : G' ⧸ H') := rfl

private theorem quotMap_injective (H' : Subgroup G') (σ : K →* G') :
    Function.Injective (quotMap H' σ) := by
  intro a b
  refine Quotient.inductionOn₂' a b (fun x y h => ?_)
  have hxy : (σ x)⁻¹ * σ y ∈ H' := QuotientGroup.eq.mp h
  refine QuotientGroup.eq.mpr ?_
  show x⁻¹ * y ∈ H'.comap σ
  rw [Subgroup.mem_comap, map_mul, map_inv]
  exact hxy

private theorem surj_quotMap_of_surjective {K G' : Type*} [Group K] [Group G'] (H' : Subgroup G')
    (σ : K →* G') (hσ : Function.Surjective σ) : Function.Surjective (quotMap H' σ) := by
  intro s
  refine Quotient.inductionOn' s (fun g' => ?_)
  obtain ⟨k, rfl⟩ := hσ g'
  exact ⟨((k : K) : K ⧸ (H'.comap σ)), rfl⟩

private theorem finiteIndex_comap_of_surjQuot {K G' : Type*} [Group K] [Group G']
    (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    (hsurj : Function.Surjective (quotMap H' σ)) : (H'.comap σ).FiniteIndex := by
  constructor
  have hcard : Nat.card (K ⧸ (H'.comap σ)) = Nat.card (G' ⧸ H') :=
    Nat.card_eq_of_bijective _ ⟨quotMap_injective H' σ, hsurj⟩
  show (H'.comap σ).index ≠ 0
  rw [Subgroup.index, hcard]
  exact Subgroup.FiniteIndex.index_ne_zero

set_option maxHeartbeats 6400000 in

private theorem coresHom_comp_apply (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    [(H'.comap σ).FiniteIndex]
    (hsurj : Function.Surjective (quotMap H' σ))
    (ψ : Additive ↥H' →+ A) (k : K) :
    coresHom H' ψ (Additive.ofMul (σ k)) =
      coresHom (H'.comap σ) (ψ.comp (AddMonoidHom.mk'
        (fun j => Additive.ofMul (⟨σ (Additive.toMul j : ↥(H'.comap σ)), (Additive.toMul j).2⟩ : ↥H'))
        (fun a b => by simp [map_mul]; rfl)))
        (Additive.ofMul k) := by
  classical
  letI := H'.fintypeQuotientOfFiniteIndex
  letI := (H'.comap σ).fintypeQuotientOfFiniteIndex
  have hbij : Function.Bijective (quotMap H' σ) := ⟨quotMap_injective H' σ, hsurj⟩
  set e : (K ⧸ (H'.comap σ)) ≃ (G' ⧸ H') := Equiv.ofBijective _ hbij with hedef
  have happ : ∀ w, e w = quotMap H' σ w := fun _ => rfl
  set R : G' ⧸ H' → G' := fun s => σ (Quotient.out (e.symm s)) with hRdef
  have hR : ∀ s, ((R s : G') : G' ⧸ H') = s := by
    intro s
    show ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H') = s
    have h1 : ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H')
        = quotMap H' σ ((Quotient.out (e.symm s) : K) : K ⧸ (H'.comap σ)) := rfl
    rw [h1, QuotientGroup.out_eq']
    rw [← happ (e.symm s)]
    exact e.apply_symm_apply s
  rw [coresHom_apply_section H' ψ R hR (σ k), coresHom_apply]
  refine (Fintype.sum_equiv e _ _ ?_).symm
  intro w
  have hsmul : (σ k) • (e w) = e (k • w) := by
    refine Quotient.inductionOn' w (fun a => ?_)
    show ((σ k * σ a : G') : G' ⧸ H') = quotMap H' σ ((k * a : K) : K ⧸ (H'.comap σ))
    rw [quotMap_mk, map_mul]
  have hRew : R (e w) = σ (Quotient.out w) := by
    show σ (Quotient.out (e.symm (e w))) = σ (Quotient.out w)
    rw [e.symm_apply_apply]
  have hRsmul : R ((σ k) • (e w)) = σ (Quotient.out (k • w)) := by
    rw [hsmul]
    show σ (Quotient.out (e.symm (e (k • w)))) = σ (Quotient.out (k • w))
    rw [e.symm_apply_apply]
  refine congrArg ψ (congrArg Additive.ofMul (Subtype.ext ?_))
  show σ ((transferAux (H'.comap σ) k w : ↥(H'.comap σ)) : K)
      = (R ((σ k) • (e w)))⁻¹ * (σ k * R (e w))
  rw [hRew, hRsmul, coe_transferAux]
  rw [map_mul, map_mul, map_inv]

end Transport
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

section Trans
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

private def mapDown (K : Subgroup G) (J : Subgroup ↥K) : ↥(J.map K.subtype) →* ↥J where
  toFun x := ⟨⟨x.1, Subgroup.map_subtype_le J x.2⟩, by
    obtain ⟨j, hjJ, hjval⟩ := x.2
    have hj : (⟨x.1, Subgroup.map_subtype_le J x.2⟩ : ↥K) = j := Subtype.ext hjval.symm
    rw [hj]; exact hjJ⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

@[scoped simp] private theorem coe_coe_mapDown (K : Subgroup G) (J : Subgroup ↥K) (x : ↥(J.map K.subtype)) :
    (((mapDown K J x : ↥J) : ↥K) : G) = (x : G) := rfl

private def projQuot (K : Subgroup G) (J : Subgroup ↥K) : G ⧸ (J.map K.subtype) → G ⧸ K :=
  Quotient.map' id (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Subgroup.map_subtype_le J hab)

@[scoped simp] private theorem projQuot_mk (K : Subgroup G) (J : Subgroup ↥K) (x : G) :
    projQuot K J ((x : G) : G ⧸ (J.map K.subtype)) = ((x : G) : G ⧸ K) := rfl

private theorem coresHom_trans (K : Subgroup G) [K.FiniteIndex] (J : Subgroup ↥K) [J.FiniteIndex]
    [(J.map K.subtype).FiniteIndex] (χ : Additive ↥J →+ A) (g : G) :
    coresHom K (coresHom J χ) (Additive.ofMul g) =
      coresHom (J.map K.subtype) (pullbackHom (mapDown K J) χ) (Additive.ofMul g) := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  letI := J.fintypeQuotientOfFiniteIndex
  set Ĵ := J.map K.subtype with hJhat
  letI := Ĵ.fintypeQuotientOfFiniteIndex

  have hfib_mem : ∀ v : G ⧸ Ĵ, (Quotient.out (projQuot K J v))⁻¹ * Quotient.out v ∈ K := by
    intro v
    refine QuotientGroup.eq.mp ?_
    have h1 : projQuot K J ((Quotient.out v : G) : G ⧸ Ĵ) = ((Quotient.out v : G) : G ⧸ K) := rfl
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' v]
    rw [h1]
  set fib : (v : G ⧸ Ĵ) → ↥K ⧸ J := fun v =>
    ((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) : ↥K ⧸ J)
    with hfibdef

  set unpair : (G ⧸ K) × (↥K ⧸ J) → G ⧸ Ĵ := fun p =>
    ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G) : G) : G ⧸ Ĵ) with hunpairdef
  have hround1 : ∀ v : G ⧸ Ĵ, unpair (projQuot K J v, fib v) = v := by
    intro v
    show ((Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G) : G) : G ⧸ Ĵ) = v
    conv_rhs => rw [← QuotientGroup.out_eq' v]
    refine (QuotientGroup.eq.mpr ?_).symm

    have hj : (Quotient.out (fib v))⁻¹
        * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) ∈ J := by
      refine QuotientGroup.eq.mp ?_
      rw [QuotientGroup.out_eq']
    have hval : (Quotient.out v)⁻¹
        * (Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G))
        = ((((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
            * Quotient.out (fib v) : ↥K) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [hval]
    refine ⟨((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
        * Quotient.out (fib v), ?_, rfl⟩
    have hflip : ((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
        * Quotient.out (fib v)
        = ((Quotient.out (fib v))⁻¹
            * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹ := by
      group
    rw [hflip]
    exact J.inv_mem hj
  have hmem_of_val : ∀ (x : ↥K), (x : G) ∈ Ĵ → x ∈ J := by
    intro x hx
    obtain ⟨j, hjJ, hjval⟩ := hx
    have hxj : x = j := Subtype.ext hjval.symm
    rw [hxj]; exact hjJ
  have hround2a : ∀ p : (G ⧸ K) × (↥K ⧸ J), projQuot K J (unpair p) = p.1 := by
    intro p
    show ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G) : G) : G ⧸ K) = p.1
    conv_rhs => rw [← QuotientGroup.out_eq' p.1]
    refine (QuotientGroup.eq.mpr ?_).symm
    rw [inv_mul_cancel_left]
    exact (Quotient.out p.2).2

  have hfib_smul : ∀ (x : G) (v : G ⧸ Ĵ),
      fib (x • v) = transferAux K x (projQuot K J v) • fib v := by
    intro x v
    have hproj : projQuot K J (x • v) = x • projQuot K J v := by
      refine Quotient.inductionOn' v (fun a => ?_)
      rfl
    show ((⟨(Quotient.out (projQuot K J (x • v)))⁻¹ * Quotient.out (x • v),
        hfib_mem (x • v)⟩ : ↥K) : ↥K ⧸ J) = _
    conv_rhs => rw [← QuotientGroup.out_eq' (fib v)]
    show _ = ((transferAux K x (projQuot K J v) * Quotient.out (fib v) : ↥K) : ↥K ⧸ J)
    refine (QuotientGroup.eq.mpr ?_).symm
    refine hmem_of_val _ ?_

    have hĵ1 : (Quotient.out v)⁻¹ * x⁻¹ * Quotient.out (x • v) ∈ Ĵ := by
      have h1 : ((x * Quotient.out v : G) : G ⧸ Ĵ) = ((Quotient.out (x • v) : G) : G ⧸ Ĵ) := by
        rw [QuotientGroup.out_eq']
        show x • ((Quotient.out v : G) : G ⧸ Ĵ) = x • v
        rw [QuotientGroup.out_eq']
      have h2 := QuotientGroup.eq.mp h1
      simpa [mul_assoc] using h2
    have hj0 : (Quotient.out (fib v))⁻¹
        * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) ∈ J := by
      refine QuotientGroup.eq.mp ?_
      rw [QuotientGroup.out_eq']

    have hval : ((((transferAux K x (projQuot K J v) * Quotient.out (fib v) : ↥K))⁻¹
          * (⟨(Quotient.out (projQuot K J (x • v)))⁻¹ * Quotient.out (x • v),
              hfib_mem (x • v)⟩ : ↥K) : ↥K) : G)
        = (((Quotient.out (fib v))⁻¹
            * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) : ↥K) : G)
          * ((Quotient.out v)⁻¹ * x⁻¹ * Quotient.out (x • v)) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_transferAux, hproj]
      group
    rw [hval]
    exact Subgroup.mul_mem _ ⟨_, hj0, rfl⟩ hĵ1

  set R : G ⧸ Ĵ → G := fun v =>
    Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G) with hRdef
  have hR : ∀ v, ((R v : G) : G ⧸ Ĵ) = v := fun v => hround1 v

  have hRg : ∀ v : G ⧸ Ĵ, R (g • v)
      = Quotient.out (g • projQuot K J v)
        * ((Quotient.out (transferAux K g (projQuot K J v) • fib v) : ↥K) : G) := by
    intro v
    show Quotient.out (projQuot K J (g • v)) * ((Quotient.out (fib (g • v)) : ↥K) : G) = _
    rw [hfib_smul g v]
    congr 2
    refine Quotient.inductionOn' v (fun a => ?_)
    rfl

  have hL : coresHom K (coresHom J χ) (Additive.ofMul g)
      = ∑ t : G ⧸ K, ∑ w : ↥K ⧸ J,
          χ (Additive.ofMul (transferAux J (transferAux K g t) w)) := by
    rw [coresHom_apply]
    exact Finset.sum_congr rfl (fun t _ => coresHom_apply J χ (transferAux K g t))
  rw [hL, coresHom_apply_section Ĵ (pullbackHom (mapDown K J) χ) R hR g]

  have hpair : ∀ v : G ⧸ Ĵ,
      (pullbackHom (mapDown K J) χ) (Additive.ofMul
        (⟨(R (g • v))⁻¹ * (g * R v), section_cocycle_mem Ĵ R hR g v⟩ : ↥Ĵ))
        = χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v))) := by
    intro v
    rw [pullbackHom_apply]
    refine (congrArg χ (congrArg Additive.ofMul (Subtype.ext (Subtype.ext ?_)))).symm
    show ((((transferAux J (transferAux K g (projQuot K J v)) (fib v) : ↥J) : ↥K)) : G)
        = (R (g • v))⁻¹ * (g * R v)
    rw [coe_transferAux, hRg v]
    simp only [hRdef, Subgroup.coe_mul, InvMemClass.coe_inv, coe_transferAux]
    group
  rw [Finset.sum_congr rfl (fun v _ => hpair v)]

  have hsum : ∑ v : G ⧸ Ĵ,
      χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v)))
        = ∑ p : (G ⧸ K) × (↥K ⧸ J),
            χ (Additive.ofMul (transferAux J (transferAux K g p.1) p.2)) := by
    refine Fintype.sum_equiv
      (⟨fun v => (projQuot K J v, fib v), unpair, hround1, fun p => ?_⟩ :
        (G ⧸ Ĵ) ≃ ((G ⧸ K) × (↥K ⧸ J)))
      _ _ (fun v => rfl)

    have h2b : fib (unpair p) = p.2 := by
      show ((⟨(Quotient.out (projQuot K J (unpair p)))⁻¹ * Quotient.out (unpair p),
          hfib_mem (unpair p)⟩ : ↥K) : ↥K ⧸ J) = p.2
      conv_rhs => rw [← QuotientGroup.out_eq' p.2]
      refine (QuotientGroup.eq.mpr ?_).symm
      refine hmem_of_val _ ?_
      have hĵ : ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G))⁻¹
          * Quotient.out (unpair p)) ∈ Ĵ := by
        refine QuotientGroup.eq.mp ?_
        rw [QuotientGroup.out_eq']
      have hval2 : (((Quotient.out p.2)⁻¹
            * (⟨(Quotient.out (projQuot K J (unpair p)))⁻¹ * Quotient.out (unpair p),
                hfib_mem (unpair p)⟩ : ↥K) : ↥K) : G)
          = (Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G))⁻¹
              * Quotient.out (unpair p) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hround2a]
        group
      rw [hval2]
      exact hĵ
    exact Prod.ext (hround2a p) h2b
  exact
    calc ∑ t : G ⧸ K, ∑ w : ↥K ⧸ J, χ (Additive.ofMul (transferAux J (transferAux K g t) w))
        = ∑ p : (G ⧸ K) × (↥K ⧸ J),
            χ (Additive.ofMul (transferAux J (transferAux K g p.1) p.2)) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ v : G ⧸ Ĵ,
            χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v))) :=
          hsum.symm

private theorem coresHom_congr {G : Type*} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ = K₂)
    [K₁.FiniteIndex] [K₂.FiniteIndex]
    (f₁ : Additive ↥K₁ →+ A) (f₂ : Additive ↥K₂ →+ A)
    (hf : ∀ (g : G) (h₁ : g ∈ K₁), f₁ (Additive.ofMul (⟨g, h₁⟩ : ↥K₁))
        = f₂ (Additive.ofMul (⟨g, h ▸ h₁⟩ : ↥K₂)))
    (x : Additive G) :
    coresHom K₁ f₁ x = coresHom K₂ f₂ x := by
  subst h
  have hext : f₁ = f₂ := AddMonoidHom.ext fun y => by
    have h := hf (Additive.toMul y : ↥K₁) (Additive.toMul y).2
    simpa using h
  rw [hext]

end Trans
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

private theorem pullbackHom_conj {G : Type*} [Group G] {A : Type*} [AddCommGroup A]
    (u : G) (φ : Additive G →+ A) :
    pullbackHom ((MulAut.conj u).toMonoidHom) φ = φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (u * Additive.toMul x * u⁻¹)) = φ x
  rw [show Additive.ofMul (u * Additive.toMul x * u⁻¹)
      = Additive.ofMul u + Additive.ofMul (Additive.toMul x) + Additive.ofMul u⁻¹ from rfl]
  rw [map_add, map_add, ofMul_inv, map_neg]
  show φ (Additive.ofMul u) + φ x + -φ (Additive.ofMul u) = φ x
  abel

section PP2
variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [AddCommGroup A]

private theorem sum_transferAux_pow (ψ : Additive ↥H →+ A) (g : G) (q : G ⧸ H) :
    ∀ n : ℕ, ∑ j ∈ Finset.range n, ψ (Additive.ofMul (transferAux H g ((g ^ j) • q)))
      = ψ (Additive.ofMul (transferAux H (g ^ n) q))
  | 0 => by
      have h1 : transferAux H (1 : G) q = 1 := by
        ext
        rw [coe_transferAux]
        simp
      rw [Finset.range_zero, Finset.sum_empty, pow_zero, h1]
      simp
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_transferAux_pow ψ g q n]
      have hc : transferAux H (g ^ (n + 1) : G) q
          = transferAux H g ((g ^ n) • q) * transferAux H (g ^ n) q := by
        rw [pow_succ']
        exact transferAux_mul H g (g ^ n) q
      rw [hc, ofMul_mul, map_add]
      abel

private theorem smul_iterate_eq (g : G) (q : G ⧸ H) :
    ∀ n : ℕ, (fun x : G ⧸ H => g • x)^[n] q = (g ^ n) • q
  | 0 => by simp
  | n + 1 => by
      rw [Function.iterate_succ_apply', smul_iterate_eq g q n, ← mul_smul, ← pow_succ']

private theorem minimalPeriod_smul_pos [H.FiniteIndex] (g : G) (q : G ⧸ H) :
    0 < Function.minimalPeriod (fun x => g • x) q := by
  letI := H.fintypeQuotientOfFiniteIndex
  apply Function.minimalPeriod_pos_of_mem_periodicPts
  rw [Function.mem_periodicPts]

  have hni : ¬ Function.Injective (fun n : ℕ => (g ^ n) • q) := fun hinj =>
    Set.infinite_range_of_injective hinj (Set.toFinite _)
  rw [Function.not_injective_iff] at hni
  obtain ⟨i, j, hij, hne⟩ := hni
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, by omega, ?_⟩
    show (fun x : G ⧸ H => g • x)^[j - i] q = q
    rw [smul_iterate_eq]
    apply MulAction.injective (g ^ i)
    show g ^ i • g ^ (j - i) • q = g ^ i • q
    rw [← mul_smul, ← pow_add, show i + (j - i) = j from by omega]
    exact hij.symm
  · refine ⟨i - j, by omega, ?_⟩
    show (fun x : G ⧸ H => g • x)^[i - j] q = q
    rw [smul_iterate_eq]
    apply MulAction.injective (g ^ j)
    show g ^ j • g ^ (i - j) • q = g ^ j • q
    rw [← mul_smul, ← pow_add, show j + (i - j) = i from by omega]
    exact hij

private theorem coresHom_vanish [H.FiniteIndex] (ψ : Additive ↥H →+ A)
    (P : G → Prop)
    (hconj : ∀ (x g : G), P g → P (x⁻¹ * g * x))
    (hpow : ∀ (g : G) (n : ℕ), 0 < n → P g → P (g ^ n))
    (hψ : ∀ h : ↥H, P (h : G) → ψ (Additive.ofMul h) = 0)
    (g : G) (hg : P g) :
    coresHom H ψ (Additive.ofMul g) = 0 := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  rw [coresHom_apply]

  rw [Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits (↥(Subgroup.zpowers g)) (G ⧸ H))
      (fun q => ψ (Additive.ofMul (transferAux H g q)))
      (fun p => ψ (Additive.ofMul (transferAux H g
        ((MulAction.selfEquivSigmaOrbits (↥(Subgroup.zpowers g)) (G ⧸ H)).symm p))))
      (fun q => by simp only [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sigma]

  refine Finset.sum_eq_zero fun ω _ => ?_
  set b := Quotient.out ω with hb
  set n := Function.minimalPeriod (fun x : G ⧸ H => g • x) b with hn
  haveI : NeZero n := ⟨(minimalPeriod_smul_pos g b).ne'⟩

  have hsymmS : ∀ y : MulAction.orbit (↥(Subgroup.zpowers g)) b,
      (MulAction.selfEquivSigmaOrbits (↥(Subgroup.zpowers g)) (G ⧸ H)).symm ⟨ω, y⟩
        = (y : G ⧸ H) := fun y => rfl
  simp only [hsymmS]

  have horb : ∑ y : MulAction.orbit (↥(Subgroup.zpowers g)) b,
      ψ (Additive.ofMul (transferAux H g (y : G ⧸ H)))
      = ∑ k : ZMod n, ψ (Additive.ofMul (transferAux H g ((g ^ (ZMod.cast k : ℤ)) • b))) := by
    refine Fintype.sum_equiv (MulAction.orbitZPowersEquiv g b) _ _ fun y => ?_
    have hy : ((MulAction.orbitZPowersEquiv g b).symm ((MulAction.orbitZPowersEquiv g b) y)
        : G ⧸ H) = (g ^ (ZMod.cast ((MulAction.orbitZPowersEquiv g b) y) : ℤ)) • b := by
      rw [MulAction.orbitZPowersEquiv_symm_apply]
      rfl
    rw [← hy, Equiv.symm_apply_apply]
  rw [horb]

  have hcast : ∀ k : ZMod n, (g ^ (ZMod.cast k : ℤ)) • b = (g ^ (ZMod.val k)) • b := by
    intro k
    rw [show (ZMod.cast k : ℤ) = ((ZMod.val k : ℕ) : ℤ) from (ZMod.natCast_val k).symm,
      zpow_natCast]
  simp only [hcast]
  have hzr : ∑ k : ZMod n, ψ (Additive.ofMul (transferAux H g ((g ^ (ZMod.val k)) • b)))
      = ∑ j ∈ Finset.range n, ψ (Additive.ofMul (transferAux H g ((g ^ j) • b))) := by
    refine Finset.sum_bij' (fun k _ => ZMod.val k) (fun j _ => (j : ZMod n)) ?_ ?_ ?_ ?_ ?_
    · intro k _
      exact Finset.mem_range.mpr (ZMod.val_lt k)
    · intro j _
      exact Finset.mem_univ _
    · intro k _
      show ((ZMod.val k : ℕ) : ZMod n) = k
      rw [ZMod.natCast_val, ZMod.cast_id]
    · intro j hj
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
    · intro k _
      rfl
  rw [hzr, sum_transferAux_pow]

  have hfix : (g ^ n) • b = b := by
    have h := Function.iterate_minimalPeriod (f := fun x : G ⧸ H => g • x) (x := b)
    rwa [smul_iterate_eq] at h
  have harg : (transferAux H (g ^ n) b : G) = b.out⁻¹ * (g ^ n * b.out) := by
    rw [coe_transferAux, hfix]
  refine hψ _ ?_
  show P ((transferAux H (g ^ n) b : G))
  rw [harg, ← mul_assoc]
  exact hconj b.out (g ^ n) (hpow g n (minimalPeriod_smul_pos g b) hg)

end PP2
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

private theorem dvd_ediv_iff_mul_dvd {b : ℤ} (q ℓ : ℤ) (hq : q ≠ 0) (hqb : q ∣ b) :
    ℓ ∣ b / q ↔ ℓ * q ∣ b := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [← Int.ediv_mul_cancel hqb, hm]
    ring
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, mul_comm ℓ q, mul_assoc, Int.mul_ediv_cancel_left _ hq]

private theorem map_comap_iotaSymm (N q ℓ : ℕ) [NeZero q] :
    ((heckeUpper (N * q) ℓ).comap ((iotaUpperEquiv N q).symm.toMonoidHom)).map
        (heckeUpper N q).subtype = heckeUpper N (ℓ * q) := by
  have hqZ : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  ext γ
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, hxℓ, rfl⟩

    have hι : Ihara.ι₁ N q ((iotaUpperEquiv N q).symm x) = (x : Gamma0 N) :=
      congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply x)
    have hb : (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        = ((((((iotaUpperEquiv N q).symm x) : Gamma0 (N * q)) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) 0 1) * (q : ℤ) := by
      rw [← hι]
      rw [show ((((Ihara.ι₁ N q ((iotaUpperEquiv N q).symm x) : Gamma0 N) : SL(2, ℤ))) :
          Matrix (Fin 2) (Fin 2) ℤ)
        = Ihara.iota1Mat q ((((iotaUpperEquiv N q).symm x : Gamma0 (N * q)) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) from Ihara.coe_coe_iota1 N q _]
      rfl
    rw [mem_heckeUpper] at hxℓ ⊢
    show ((ℓ * q : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
    rw [hb]
    push_cast
    exact mul_dvd_mul_right hxℓ _
  · intro hγ
    rw [mem_heckeUpper] at hγ
    have hqb : ((q : ℕ) : ℤ) ∣ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 := by
      refine dvd_trans ?_ hγ
      push_cast
      exact Dvd.intro_left _ rfl
    refine ⟨⟨γ, (mem_heckeUpper N q).mpr hqb⟩, ?_, rfl⟩

    have hι : Ihara.ι₁ N q ((iotaUpperEquiv N q).symm ⟨γ, (mem_heckeUpper N q).mpr hqb⟩)
        = γ :=
      congrArg Subtype.val
        ((iotaUpperEquiv N q).apply_symm_apply ⟨γ, (mem_heckeUpper N q).mpr hqb⟩)
    have hb : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
        = (((((iotaUpperEquiv N q).symm ⟨γ, (mem_heckeUpper N q).mpr hqb⟩ :
              Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) * (q : ℤ) := by
      conv_lhs => rw [← hι]
      rw [show ((((Ihara.ι₁ N q ((iotaUpperEquiv N q).symm
            ⟨γ, (mem_heckeUpper N q).mpr hqb⟩) : Gamma0 N) : SL(2, ℤ))) :
          Matrix (Fin 2) (Fin 2) ℤ)
        = Ihara.iota1Mat q ((((iotaUpperEquiv N q).symm
              ⟨γ, (mem_heckeUpper N q).mpr hqb⟩ : Gamma0 (N * q)) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) from Ihara.coe_coe_iota1 N q _]
      rfl
    rw [mem_heckeUpper]
    rw [hb] at hγ
    push_cast at hγ
    exact (mul_dvd_mul_iff_right hqZ).mp hγ

private theorem map_comap_heckeConj (N ℓ q : ℕ) [NeZero ℓ] :
    ((heckeUpper N q).comap (heckeConj N ℓ)).map (heckeUpper N ℓ).subtype
      = heckeUpper N (q * ℓ) := by
  have hℓZ : ((ℓ : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  ext γ
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, hxq, rfl⟩
    have hxℓ : ((ℓ : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
      (mem_heckeUpper N ℓ).mp x.2
    rw [mem_heckeUpper] at hxq
    rw [show (((heckeConj N ℓ x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = heckeConjMat ℓ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) from rfl,
      heckeConjMat_apply_zero_one] at hxq
    show ((q * ℓ : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
    push_cast
    exact (dvd_ediv_iff_mul_dvd (ℓ : ℤ) (q : ℤ) hℓZ hxℓ).mp hxq
  · intro hγ
    rw [mem_heckeUpper] at hγ
    have hℓb : ((ℓ : ℕ) : ℤ) ∣ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 := by
      refine dvd_trans ?_ hγ
      push_cast
      exact dvd_mul_left _ _
    refine ⟨⟨γ, (mem_heckeUpper N ℓ).mpr hℓb⟩, ?_, rfl⟩
    rw [mem_heckeUpper]
    rw [show (((heckeConj N ℓ ⟨γ, (mem_heckeUpper N ℓ).mpr hℓb⟩ : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ)
        = heckeConjMat ℓ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) from rfl,
      heckeConjMat_apply_zero_one]
    refine (dvd_ediv_iff_mul_dvd (ℓ : ℤ) (q : ℤ) hℓZ hℓb).mpr ?_
    push_cast at hγ
    exact hγ

private theorem surj_quotMap_heckeConj (N ℓ q' : ℕ) [NeZero N] [NeZero ℓ] [NeZero q']
    (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) (hℓ : ℓ.Prime) (hℓNq' : ¬ ℓ ∣ N * q') :
    Function.Surjective (quotMap (heckeUpper N q') (heckeConj N ℓ)) := by
  haveI : Fact q'.Prime := ⟨hq'⟩
  intro s
  refine Quotient.inductionOn' s (fun γ => ?_)
  set b : ℤ := (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 with hbdef
  set d : ℤ := (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 with hddef

  have hgoal : ∀ (k : ↥(heckeUpper N ℓ)),
      ((q' : ℤ) ∣ ((((heckeConj N ℓ k)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 0 1) →
      ∃ w, quotMap (heckeUpper N q') (heckeConj N ℓ) w = Quotient.mk'' γ := by
    intro k hdvd
    refine ⟨((k : ↥(heckeUpper N ℓ)) : ↥(heckeUpper N ℓ) ⧸ _), ?_⟩
    rw [quotMap_mk]
    exact QuotientGroup.eq.mpr ((mem_heckeUpper N q').mpr hdvd)

  have hprod : ∀ (k : ↥(heckeUpper N ℓ)),
      ((((heckeConj N ℓ k)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        = (((heckeConj N ℓ k : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b
          - (((heckeConj N ℓ k : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * d := by
    intro k
    have hmul : ((((heckeConj N ℓ k)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ)
        = (((((heckeConj N ℓ k : Gamma0 N) : SL(2, ℤ)))⁻¹ : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ)
          * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [hmul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    show (((heckeConj N ℓ k : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b
        + -(((heckeConj N ℓ k : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * d = _
    ring
  by_cases hd : ((d : ZMod q') = 0)
  ·
    have hcop : IsCoprime ((q' : ℕ) : ℤ) (((N * ℓ * ℓ : ℕ) : ℤ)) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      refine (Nat.Prime.coprime_iff_not_dvd hq').mpr ?_
      intro hdvd
      rcases (Nat.Prime.dvd_mul hq').mp hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq').mp h with h' | h'
        · exact hq'N h'
        · exact hℓNq' (by
            have : q' = ℓ := ((Nat.prime_dvd_prime_iff_eq hq' hℓ).mp h')
            rw [← this]; exact Dvd.intro_left N rfl)
      · exact hℓNq' (by
          have : q' = ℓ := ((Nat.prime_dvd_prime_iff_eq hq' hℓ).mp h)
          rw [← this]; exact Dvd.intro_left N rfl)
    obtain ⟨α, β, hαβ⟩ := hcop
    have hdet : Matrix.det !![α, -β * (ℓ : ℤ); (N : ℤ) * ℓ, ((q' : ℕ) : ℤ)] = 1 := by
      rw [Matrix.det_fin_two_of]
      push_cast at hαβ
      linear_combination hαβ
    have hkΓ : (⟨!![α, -β * (ℓ : ℤ); (N : ℤ) * ℓ, ((q' : ℕ) : ℤ)], hdet⟩ : SL(2, ℤ)) ∈ Gamma0 N := by
      refine Gamma0_mem.mpr ?_
      show ((((N : ℤ) * ℓ) : ℤ) : ZMod N) = 0
      push_cast
      simp
    have hkU : (⟨⟨!![α, -β * (ℓ : ℤ); (N : ℤ) * ℓ, ((q' : ℕ) : ℤ)], hdet⟩, hkΓ⟩ : Gamma0 N)
        ∈ heckeUpper N ℓ := by
      rw [mem_heckeUpper]
      show ((ℓ : ℕ) : ℤ) ∣ -β * (ℓ : ℤ)
      exact dvd_mul_left _ _
    refine hgoal ⟨_, hkU⟩ ?_
    rw [hprod]
    have h11 : (((heckeConj N ℓ ⟨_, hkU⟩ : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((q' : ℕ) : ℤ) := by
      show heckeConjMat ℓ _ 1 1 = _
      rw [heckeConjMat_apply_one_one]
      rfl
    have h01 : (((heckeConj N ℓ ⟨_, hkU⟩ : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -β := by
      show heckeConjMat ℓ _ 0 1 = -β
      rw [heckeConjMat_apply_zero_one]
      show -β * (ℓ : ℤ) / (ℓ : ℤ) = -β
      exact Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
    rw [h11, h01]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_self, hd]
    ring
  ·
    have hq'd : ¬ ((q' : ℕ) : ℤ) ∣ d := fun hdvd =>
      hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d q').mpr hdvd)
    have hq'dabs : ¬ q' ∣ d.natAbs := fun h => hq'd (Int.natCast_dvd.mpr h)
    have hcop2 : IsCoprime (((q' : ℕ) : ℤ)) d := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      show (Int.natAbs ((q' : ℕ) : ℤ)).gcd d.natAbs = 1
      rw [Int.natAbs_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hq').mpr hq'dabs
    obtain ⟨u, v, huv⟩ := hcop2
    have hdet : Matrix.det !![(1 : ℤ), (b * v) * ℓ; 0, 1] = 1 := by
      rw [Matrix.det_fin_two_of]
      ring
    have hkΓ : (⟨!![(1 : ℤ), (b * v) * ℓ; 0, 1], hdet⟩ : SL(2, ℤ)) ∈ Gamma0 N := by
      refine Gamma0_mem.mpr ?_
      show ((0 : ℤ) : ZMod N) = 0
      simp
    have hkU : (⟨⟨!![(1 : ℤ), (b * v) * ℓ; 0, 1], hdet⟩, hkΓ⟩ : Gamma0 N)
        ∈ heckeUpper N ℓ := by
      rw [mem_heckeUpper]
      show ((ℓ : ℕ) : ℤ) ∣ (b * v) * ℓ
      exact dvd_mul_left _ _
    refine hgoal ⟨_, hkU⟩ ?_
    rw [hprod]
    have h11 : (((heckeConj N ℓ ⟨_, hkU⟩ : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
      show heckeConjMat ℓ _ 1 1 = 1
      rw [heckeConjMat_apply_one_one]
      rfl
    have h01 : (((heckeConj N ℓ ⟨_, hkU⟩ : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) 0 1 = b * v := by
      show heckeConjMat ℓ _ 0 1 = b * v
      rw [heckeConjMat_apply_zero_one]
      show (b * v) * (ℓ : ℤ) / (ℓ : ℤ) = b * v
      exact Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
    rw [h11, h01]
    exact ⟨b * u, by linear_combination (-b) * huv⟩

private theorem heckeConj_iotaSymm_swap (N q' ℓ : ℕ) [NeZero q'] [NeZero ℓ]
    (γ : Gamma0 N) (hγ : γ ∈ heckeUpper N (ℓ * q'))
    (hγq' : γ ∈ heckeUpper N q') (hγℓ : γ ∈ heckeUpper N ℓ)
    (hmem₁ : (iotaUpperEquiv N q').symm ⟨γ, hγq'⟩ ∈ heckeUpper (N * q') ℓ)
    (hmem₂ : heckeConj N ℓ ⟨γ, hγℓ⟩ ∈ heckeUpper N q') :
    heckeConj (N * q') ℓ ⟨(iotaUpperEquiv N q').symm ⟨γ, hγq'⟩, hmem₁⟩
      = (iotaUpperEquiv N q').symm ⟨heckeConj N ℓ ⟨γ, hγℓ⟩, hmem₂⟩ := by
  have hq'Z : ((q' : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q')
  have hℓZ : ((ℓ : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  obtain ⟨m, hm⟩ := (mem_heckeUpper N (ℓ * q')).mp hγ
  refine Subtype.ext (Subtype.ext ?_)
  show heckeConjMat ℓ (((((iotaUpperEquiv N q').symm ⟨γ, hγq'⟩ : Gamma0 (N * q')) :
      SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
    = (((((iotaUpperEquiv N q').symm ⟨heckeConj N ℓ ⟨γ, hγℓ⟩, hmem₂⟩ :
        Gamma0 (N * q')) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
  rw [coe_iotaUpperEquiv_symm N q' ⟨γ, hγq'⟩, coe_iotaUpperEquiv_symm N q'
    ⟨heckeConj N ℓ ⟨γ, hγℓ⟩, hmem₂⟩]
  have hconjmat : (((heckeConj N ℓ ⟨γ, hγℓ⟩ : Gamma0 N) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)
      = heckeConjMat ℓ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := rfl
  rw [hconjmat]
  have hmz : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
      = (ℓ : ℤ) * (q' : ℤ) * m := by
    push_cast at hm
    linarith [hm]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [heckeConjMat]
  · show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / (q' : ℤ)) / (ℓ : ℤ)
        = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / (ℓ : ℤ)) / (q' : ℤ)
    rw [hmz]
    rw [show (ℓ : ℤ) * (q' : ℤ) * m = (q' : ℤ) * ((ℓ : ℤ) * m) by ring,
      Int.mul_ediv_cancel_left _ hq'Z, Int.mul_ediv_cancel_left _ hℓZ]
    rw [show (q' : ℤ) * ((ℓ : ℤ) * m) = (ℓ : ℤ) * ((q' : ℤ) * m) by ring,
      Int.mul_ediv_cancel_left _ hℓZ, Int.mul_ediv_cancel_left _ hq'Z]
  · show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (q' : ℤ)) * (ℓ : ℤ)
        = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (ℓ : ℤ)) * (q' : ℤ)
    ring
  · simp [heckeConjMat]

private theorem trace_conj {N : ℕ} (x γ : Gamma0 N) :
    ((((x⁻¹ * γ * x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace
      = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace := by
  have h1 : (((x⁻¹ * γ * x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((((x : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [h1, Matrix.trace_mul_comm, ← mul_assoc]
  have h2 : (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      ((((x : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    have h := mul_inv_cancel ((x : Gamma0 N) : SL(2, ℤ))
    calc (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((((x : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = ((((x : Gamma0 N) : SL(2, ℤ)) * ((x : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ))
          : Matrix (Fin 2) (Fin 2) ℤ) := rfl
      _ = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h]; rfl
  rw [h2, one_mul]

private theorem sl2_sq (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = 1) :
    m * m = m.trace • m - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Matrix.one_apply, smul_eq_mul]
    norm_num
    linear_combination -hdet
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Matrix.one_apply, smul_eq_mul]
    norm_num
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Matrix.one_apply, smul_eq_mul]
    norm_num
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Matrix.one_apply, smul_eq_mul]
    norm_num
    linear_combination -hdet

private theorem trace_pow_rec (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = 1) (j : ℕ) :
    (m ^ (j + 2)).trace = m.trace * (m ^ (j + 1)).trace - (m ^ j).trace := by
  have h : m ^ (j + 2) = m.trace • (m ^ (j + 1)) - m ^ j := by
    calc m ^ (j + 2) = m ^ j * (m * m) := by rw [pow_add, sq]
      _ = m ^ j * (m.trace • m - 1) := by rw [sl2_sq m hdet]
      _ = m.trace • (m ^ j * m) - m ^ j * 1 := by
          rw [mul_sub, Matrix.mul_smul]
      _ = m.trace • (m ^ (j + 1)) - m ^ j := by rw [mul_one, ← pow_succ]
  rw [h, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

private theorem trace_pow_sq_eq_four {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : m.det = 1)
    (ht : m.trace ^ 2 = 4) : ∀ j : ℕ, (m ^ j).trace ^ 2 = 4 := by
  have htrone : (1 : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    simp
  have ht' : m.trace = 2 ∨ m.trace = -2 := by
    have h4 : (m.trace - 2) * (m.trace + 2) = 0 := by linear_combination ht
    rcases mul_eq_zero.mp h4 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases ht' with h2 | h2
  · have key : ∀ j : ℕ, (m ^ j).trace = 2 ∧ (m ^ (j + 1)).trace = 2 := by
      intro j
      induction j with
      | zero => exact ⟨by rw [pow_zero, htrone], by rw [pow_one, h2]⟩
      | succ i ih =>
          refine ⟨ih.2, ?_⟩
          rw [trace_pow_rec m hdet i, ih.1, ih.2, h2]
          norm_num
    intro j
    rw [(key j).1]
    norm_num
  · have key : ∀ j : ℕ, (m ^ j).trace = 2 * (-1 : ℤ) ^ j ∧
        (m ^ (j + 1)).trace = 2 * (-1 : ℤ) ^ (j + 1) := by
      intro j
      induction j with
      | zero => exact ⟨by rw [pow_zero, htrone]; norm_num, by rw [pow_one, h2]; norm_num⟩
      | succ i ih =>
          refine ⟨ih.2, ?_⟩
          rw [trace_pow_rec m hdet i, ih.1, ih.2, h2]
          ring
    intro j
    rw [(key j).1]
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow]
      norm_num
    · rw [ho.neg_one_pow]
      norm_num

private theorem gamma0_coe_pow {N : ℕ} (γ : Gamma0 N) : ∀ m : ℕ,
    (((γ ^ m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ m
  | 0 => rfl
  | m + 1 => by
      rw [pow_succ, pow_succ, ← gamma0_coe_pow γ m]
      rfl

section HBeta
variable (N q' : ℕ) [NeZero N] [NeZero q']

set_option maxHeartbeats 6400000 in

private theorem degeneracyTransfer₁_heckeOperatorHom_comm (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNq' : ¬ ℓ ∣ N * q')
    (A : Type*) [AddCommGroup A]
    (x : Additive (Gamma0 (N * q')) →+ A) (y : Additive (Gamma0 N)) :
    degeneracyTransfer₁ N q' A (heckeOperatorHom (N * q') ℓ A x) y
      = heckeOperatorHom N ℓ A (degeneracyTransfer₁ N q' A x) y := by
  classical
  haveI : NeZero (ℓ * q') := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q')⟩
  haveI : NeZero (q' * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne q') (NeZero.ne ℓ)⟩
  set σ₁ : ↥(heckeUpper N q') →* Gamma0 (N * q') :=
    (iotaUpperEquiv N q').symm.toMonoidHom with hσ₁
  set σ₂ : ↥(heckeUpper N ℓ) →* Gamma0 N := heckeConj N ℓ with hσ₂
  have hsurj₁ : Function.Surjective (quotMap (heckeUpper (N * q') ℓ) σ₁) :=
    surj_quotMap_of_surjective _ _ (iotaUpperEquiv N q').symm.surjective
  have hsurj₂ : Function.Surjective (quotMap (heckeUpper N q') σ₂) :=
    surj_quotMap_heckeConj N ℓ q' hq' hq'N hℓ hℓNq'
  haveI hJ₁fi : ((heckeUpper (N * q') ℓ).comap σ₁).FiniteIndex :=
    finiteIndex_comap_of_surjQuot _ _ hsurj₁
  haveI hJ₂fi : ((heckeUpper N q').comap σ₂).FiniteIndex :=
    finiteIndex_comap_of_surjQuot _ _ hsurj₂
  haveI hM₁fi : (((heckeUpper (N * q') ℓ).comap σ₁).map (heckeUpper N q').subtype).FiniteIndex := by
    rw [map_comap_iotaSymm]
    infer_instance
  haveI hM₂fi : (((heckeUpper N q').comap σ₂).map (heckeUpper N ℓ).subtype).FiniteIndex := by
    rw [map_comap_heckeConj]
    infer_instance

  set Ψ₁ : Additive ↥((heckeUpper (N * q') ℓ).comap σ₁) →+ A :=
    (pullbackHom (heckeConj (N * q') ℓ) x).comp (AddMonoidHom.mk'
      (fun j => Additive.ofMul (⟨σ₁ (Additive.toMul j : ↥((heckeUpper (N * q') ℓ).comap σ₁)),
        (Additive.toMul j).2⟩ : ↥(heckeUpper (N * q') ℓ)))
      (fun a b => by simp [map_mul]; rfl)) with hΨ₁
  set Ψ₂ : Additive ↥((heckeUpper N q').comap σ₂) →+ A :=
    (pullbackHom σ₁ x).comp (AddMonoidHom.mk'
      (fun j => Additive.ofMul (⟨σ₂ (Additive.toMul j : ↥((heckeUpper N q').comap σ₂)),
        (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
      (fun a b => by simp [map_mul]; rfl)) with hΨ₂

  have hΦ₁ : pullbackHom σ₁ (coresHom (heckeUpper (N * q') ℓ)
      (pullbackHom (heckeConj (N * q') ℓ) x))
      = coresHom ((heckeUpper (N * q') ℓ).comap σ₁) Ψ₁ := by
    refine AddMonoidHom.ext fun w => ?_
    show coresHom (heckeUpper (N * q') ℓ) (pullbackHom (heckeConj (N * q') ℓ) x)
        (Additive.ofMul (σ₁ (Additive.toMul w))) = _
    rw [coresHom_comp_apply (heckeUpper (N * q') ℓ) σ₁ hsurj₁
      (pullbackHom (heckeConj (N * q') ℓ) x) (Additive.toMul w)]
    rfl
  have hΦ₂ : pullbackHom σ₂ (coresHom (heckeUpper N q') (pullbackHom σ₁ x))
      = coresHom ((heckeUpper N q').comap σ₂) Ψ₂ := by
    refine AddMonoidHom.ext fun w => ?_
    show coresHom (heckeUpper N q') (pullbackHom σ₁ x)
        (Additive.ofMul (σ₂ (Additive.toMul w))) = _
    rw [coresHom_comp_apply (heckeUpper N q') σ₂ hsurj₂ (pullbackHom σ₁ x)
      (Additive.toMul w)]
    rfl

  have hL : degeneracyTransfer₁ N q' A (heckeOperatorHom (N * q') ℓ A x) y
      = coresHom (((heckeUpper (N * q') ℓ).comap σ₁).map (heckeUpper N q').subtype)
          (pullbackHom (mapDown _ _) Ψ₁) y := by
    refine Eq.trans ?_ (coresHom_trans (heckeUpper N q')
      ((heckeUpper (N * q') ℓ).comap σ₁) Ψ₁ (Additive.toMul y))
    show coresHom (heckeUpper N q')
        (pullbackHom σ₁ (coresHom (heckeUpper (N * q') ℓ)
          (pullbackHom (heckeConj (N * q') ℓ) x))) y = _
    exact congrArg (fun Φ => coresHom (heckeUpper N q') Φ y) hΦ₁
  have hR : heckeOperatorHom N ℓ A (degeneracyTransfer₁ N q' A x) y
      = coresHom (((heckeUpper N q').comap σ₂).map (heckeUpper N ℓ).subtype)
          (pullbackHom (mapDown _ _) Ψ₂) y := by
    refine Eq.trans ?_ (coresHom_trans (heckeUpper N ℓ)
      ((heckeUpper N q').comap σ₂) Ψ₂ (Additive.toMul y))
    show coresHom (heckeUpper N ℓ)
        (pullbackHom σ₂ (coresHom (heckeUpper N q') (pullbackHom σ₁ x))) y = _
    exact congrArg (fun Φ => coresHom (heckeUpper N ℓ) Φ y) hΦ₂
  refine hL.trans (Eq.trans ?_ hR.symm)

  have hKeq : (((heckeUpper (N * q') ℓ).comap σ₁).map (heckeUpper N q').subtype)
      = (((heckeUpper N q').comap σ₂).map (heckeUpper N ℓ).subtype) := by
    rw [map_comap_iotaSymm, map_comap_heckeConj]
    exact congrArg (heckeUpper N) (Nat.mul_comm ℓ q')
  refine coresHom_congr hKeq _ _ (fun γ hγ₁ => ?_) y

  have hγup : γ ∈ heckeUpper N (ℓ * q') := by
    rw [← map_comap_iotaSymm N q' ℓ]
    exact hγ₁
  obtain ⟨m, hm⟩ := (mem_heckeUpper N (ℓ * q')).mp hγup
  have hγq' : γ ∈ heckeUpper N q' := (mem_heckeUpper N q').mpr
    ⟨(ℓ : ℤ) * m, by push_cast at hm ⊢; linarith⟩
  have hγℓ : γ ∈ heckeUpper N ℓ := (mem_heckeUpper N ℓ).mpr
    ⟨(q' : ℤ) * m, by push_cast at hm ⊢; linarith⟩
  have hmem₁ : (iotaUpperEquiv N q').symm ⟨γ, hγq'⟩ ∈ heckeUpper (N * q') ℓ := by
    obtain ⟨j, hjJ, hjval⟩ := hγ₁
    have hj : j = ⟨γ, hγq'⟩ := Subtype.ext hjval
    rw [← hj]
    exact Subgroup.mem_comap.mp hjJ
  have hmem₂ : heckeConj N ℓ ⟨γ, hγℓ⟩ ∈ heckeUpper N q' := by
    have hγ₂ : γ ∈ (((heckeUpper N q').comap σ₂).map (heckeUpper N ℓ).subtype) := hKeq ▸ hγ₁
    obtain ⟨j, hjJ, hjval⟩ := hγ₂
    have hj : j = ⟨γ, hγℓ⟩ := Subtype.ext hjval
    rw [← hj]
    exact Subgroup.mem_comap.mp hjJ
  have hswap := heckeConj_iotaSymm_swap N q' ℓ γ hγup hγq' hγℓ hmem₁ hmem₂
  show x (Additive.ofMul (heckeConj (N * q') ℓ
      ⟨(iotaUpperEquiv N q').symm ⟨γ, hγq'⟩, hmem₁⟩))
    = x (Additive.ofMul ((iotaUpperEquiv N q').symm
      ⟨heckeConj N ℓ ⟨γ, hγℓ⟩, hmem₂⟩))
  exact congrArg x (congrArg Additive.ofMul hswap)

end HBeta
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

private theorem isParabolicHom_pullback_iota0 {N q : ℕ} {A : Type*} [AddCommGroup A]
    {φ : Additive (Gamma0 N) →+ A}
    (hφ : ModularCurve.Period.IsParabolicHom (Gamma0 N) φ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) (pullbackHom (Ihara.ι₀ N q) φ) := by
  intro γ htr
  show φ (Additive.ofMul (Ihara.ι₀ N q γ)) = 0
  exact hφ (Ihara.ι₀ N q γ) htr

private theorem trace_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    (((Ihara.ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Ihara.coe_coe_iota1]
  simp [Matrix.trace_fin_two, Ihara.iota1Mat]

private theorem isParabolicHom_pullback_iota1 {N q : ℕ} {A : Type*} [AddCommGroup A]
    {φ : Additive (Gamma0 N) →+ A}
    (hφ : ModularCurve.Period.IsParabolicHom (Gamma0 N) φ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) (pullbackHom (Ihara.ι₁ N q) φ) := by
  intro γ htr
  show φ (Additive.ofMul (Ihara.ι₁ N q γ)) = 0
  exact hφ (Ihara.ι₁ N q γ) (by rw [trace_iota1]; exact htr)

private theorem isParabolicHom_degeneracyTransfer₁ {N q : ℕ} [NeZero q] {A : Type*} [AddCommGroup A]
    {ψ : Additive (Gamma0 (N * q)) →+ A}
    (hψ : ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) ψ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 N) (degeneracyTransfer₁ N q A ψ) := by
  intro g htr
  show coresHom (heckeUpper N q)
      ((pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom)) ψ) (Additive.ofMul g) = 0
  refine coresHom_vanish _
    (fun γ : Gamma0 N => (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 = 4)
    (fun x γ hγ => by
      show ((((x⁻¹ * γ * x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 = 4
      rw [trace_conj]
      exact hγ)
    (fun γ m _ hγ => ?_) (fun h hPh => ?_) g htr
  · show ((((γ ^ m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 = 4
    rw [gamma0_coe_pow γ m]
    exact trace_pow_sq_eq_four ((((γ : Gamma0 N) : SL(2, ℤ))).2) hγ m
  · show ψ (Additive.ofMul ((iotaUpperEquiv N q).symm.toMonoidHom h)) = 0
    refine hψ _ ?_
    have h1 : Ihara.ι₁ N q ((iotaUpperEquiv N q).symm h) = (h : Gamma0 N) :=
      congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply h)
    have h2 := trace_iota1 N q ((iotaUpperEquiv N q).symm h)
    rw [h1] at h2
    show ((((iotaUpperEquiv N q).symm h : Gamma0 (N * q)) : SL(2, ℤ))
        : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [← h2]
    exact hPh

private theorem isParabolicHom_pullback_alConjHom {N q : ℕ} [NeZero q] {A : Type*} [AddCommGroup A]
    (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    {ψ : Additive (Gamma0 (N * q)) →+ A}
    (hψ : ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) ψ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) (pullbackHom (alConjHom N q u hu) ψ) := by
  intro γ htr
  show ψ (Additive.ofMul (alConjHom N q u hu γ)) = 0
  refine hψ _ ?_
  have h2 := trace_iota1 N q (alConjHom N q u hu γ)
  rw [iota1_alConjHom N q u hu γ] at h2
  have h3 : ((((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ)).trace
      = (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    have h := trace_conj (N := N) u⁻¹ (Ihara.ι₀ N q γ)
    simpa using h
  rw [h3] at h2
  have h4 : ((((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace
      = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace := rfl
  rw [h4] at h2
  show ((((alConjHom N q u hu γ : Gamma0 (N * q)) : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 = 4
  rw [← h2]
  exact htr

private theorem isParabolicHom_degeneracyTransfer₀Aux {N q : ℕ} [NeZero q] {A : Type*} [AddCommGroup A]
    (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    {ψ : Additive (Gamma0 (N * q)) →+ A}
    (hψ : ModularCurve.Period.IsParabolicHom (Gamma0 (N * q)) ψ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 N) (degeneracyTransfer₀Aux N q A u hu ψ) :=
  isParabolicHom_degeneracyTransfer₁ (isParabolicHom_pullback_alConjHom u hu hψ)

section E4
variable (N q : ℕ) [NeZero q]

private theorem pullback_alConjHom_pullback_iota1 (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1)
    {A : Type*} [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (alConjHom N q (bezoutConjugator N q a b hab) (bezoutConjugator_heckeUpper_dvd N q a b hab))
      (pullbackHom (Ihara.ι₁ N q) φ)
      = pullbackHom (Ihara.ι₀ N q) φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (Ihara.ι₁ N q (alConjHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab) (Additive.toMul x))))
    = φ (Additive.ofMul (Ihara.ι₀ N q (Additive.toMul x)))
  rw [iota1_alConjHom]
  rw [show Additive.ofMul ((bezoutConjugator N q a b hab : Gamma0 N) *
      Ihara.ι₀ N q (Additive.toMul x) * (bezoutConjugator N q a b hab)⁻¹)
    = Additive.ofMul (bezoutConjugator N q a b hab : Gamma0 N)
      + Additive.ofMul (Ihara.ι₀ N q (Additive.toMul x))
      + Additive.ofMul ((bezoutConjugator N q a b hab : Gamma0 N))⁻¹ from rfl]
  rw [map_add, map_add, ofMul_inv, map_neg]
  abel

private theorem degeneracyTransfer₀Aux_res0_eq_degeneracyTransfer₁_res1 (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1)
    {A : Type*} [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A) :
    degeneracyTransfer₀Aux N q A (bezoutConjugator N q a b hab) (bezoutConjugator_heckeUpper_dvd N q a b hab)
      (pullbackHom (Ihara.ι₀ N q) φ)
      = degeneracyTransfer₁ N q A (pullbackHom (Ihara.ι₁ N q) φ) := by
  show degeneracyTransfer₁ N q A (pullbackHom (alConjHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab)) (pullbackHom (Ihara.ι₀ N q) φ)) = _
  congr 1
  rw [← pullback_alConjHom_pullback_iota1 N q a b hab φ]
  refine AddMonoidHom.ext fun x => ?_
  show (pullbackHom (Ihara.ι₁ N q) φ) (Additive.ofMul (alConjHom N q
      (bezoutConjugator N q a b hab) (bezoutConjugator_heckeUpper_dvd N q a b hab)
        (alConjHom N q (bezoutConjugator N q a b hab) (bezoutConjugator_heckeUpper_dvd N q a b hab)
          (Additive.toMul x))))
    = (pullbackHom (Ihara.ι₁ N q) φ) x
  rw [alConjHom_bezout_sq N q a b hab]
  rw [show Additive.ofMul (alConjSqElt N q a b hab * Additive.toMul x *
      (alConjSqElt N q a b hab)⁻¹)
    = Additive.ofMul (alConjSqElt N q a b hab) + Additive.ofMul (Additive.toMul x)
      + Additive.ofMul ((alConjSqElt N q a b hab))⁻¹ from rfl]
  rw [map_add, map_add, ofMul_inv, map_neg]
  show
    (pullbackHom (Ihara.ι₁ N q) φ) (Additive.ofMul (alConjSqElt N q a b hab))
      + (pullbackHom (Ihara.ι₁ N q) φ) (Additive.ofMul (Additive.toMul x))
      + -(pullbackHom (Ihara.ι₁ N q) φ) (Additive.ofMul (alConjSqElt N q a b hab))
    = (pullbackHom (Ihara.ι₁ N q) φ) x
  abel_nf
  rfl

end E4
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine"

end INHX2
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

end EngineInline
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

namespace INH
namespace D6

private noncomputable abbrev RES0 (N q' : ℕ) : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ) :=
  pullbackHom (Ihara.ι₀ N q')

private noncomputable abbrev RES1 (N q' : ℕ) : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ) :=
  pullbackHom (Ihara.ι₁ N q')

private noncomputable abbrev BETA1 (N q' : ℕ) [NeZero q'] :
    (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ) :=
  degeneracyTransfer₁ N q' ℤ

private noncomputable abbrev BETA0 (N q' : ℕ) [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ) :=
  degeneracyTransfer₀ N q' ℤ hq' hq'N

section Plumbing

variable {N q' : ℕ}

private theorem hTpar_int : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
    ModularCurve.Period.IsParabolicHom (Gamma0 M) φ →
      ModularCurve.Period.IsParabolicHom (Gamma0 M) (heckeOperatorHom M ℓ ℤ φ) :=
  fun M ℓ _ φ hφ => ModularCurve.Period.heckeOperatorHom_preserves_parabolic M ℓ ℤ φ hφ

private theorem hres0 : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
    ∀ φ : Additive (Gamma0 N) →+ ℤ,
      RES0 N q' (heckeOperatorHom N ℓ ℤ φ) = heckeOperatorHom (N * q') ℓ ℤ (RES0 N q' φ) :=
  fun ℓ _ hℓ hℓNq φ =>
    heckeOperatorHom_pullback_iota0 N q' ℓ hℓ (fun h => hℓNq (Dvd.dvd.mul_left h N)) φ

private theorem hres1 : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
    ∀ φ : Additive (Gamma0 N) →+ ℤ,
      RES1 N q' (heckeOperatorHom N ℓ ℤ φ) = heckeOperatorHom (N * q') ℓ ℤ (RES1 N q' φ) :=
  fun ℓ _ hℓ hℓNq φ =>
    heckeOperatorHom_pullback_iota1 N q' ℓ hℓ (fun h => hℓNq (Dvd.dvd.mul_left h N)) φ

private theorem hrespar0 : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
    RES0 N q' φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ :=
  fun _ hφ => INHX2.isParabolicHom_pullback_iota0 hφ

private theorem hrespar1 : ∀ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
    RES1 N q' φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ :=
  fun _ hφ => INHX2.isParabolicHom_pullback_iota1 hφ

private theorem hbetapar1 [NeZero q'] : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
    BETA1 N q' x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
  fun _ hx => INHX2.isParabolicHom_degeneracyTransfer₁ hx

private theorem hbetapar0 [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      BETA0 N q' hq' hq'N x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
  fun _ hx => INHX2.isParabolicHom_degeneracyTransfer₀Aux _ _ hx

private theorem hbeta1 [NeZero N] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
      ∀ x : Additive (Gamma0 (N * q')) →+ ℤ,
        BETA1 N q' (heckeOperatorHom (N * q') ℓ ℤ x) = heckeOperatorHom N ℓ ℤ (BETA1 N q' x) :=
  fun ℓ _ hℓ hℓNq x => AddMonoidHom.ext fun y =>
    INHX2.degeneracyTransfer₁_heckeOperatorHom_comm N q' hq' hq'N ℓ hℓ hℓNq ℤ x y

private theorem hentry10 [NeZero q'] : ∀ y : Additive (Gamma0 N) →+ ℤ,
    BETA1 N q' (RES0 N q' y) = heckeOperatorHom N q' ℤ y :=
  fun y => degeneracyTransfer₁_pullback_iota0 N q' ℤ y

private theorem hentry01 [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ y : Additive (Gamma0 N) →+ ℤ, BETA0 N q' hq' hq'N (RES1 N q' y) = heckeOperatorHom N q' ℤ y :=
  fun y => degeneracyTransfer₀Aux_pullback_iota1 N q' ℤ _ _ y

private theorem pullback_symm_pullback_iota1 [NeZero q'] {A : Type*} [AddCommGroup A]
    (y : Additive (Gamma0 N) →+ A) :
    pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom) (pullbackHom (Ihara.ι₁ N q') y) =
      resHom (heckeUpper N q') y := by
  refine AddMonoidHom.ext fun x => ?_
  show y (Additive.ofMul (Ihara.ι₁ N q' ((iotaUpperEquiv N q').symm (Additive.toMul x)))) =
    y (Additive.ofMul ((Additive.toMul x : heckeUpper N q') : Gamma0 N))
  congr 2
  show ((iotaUpperEquiv N q' ((iotaUpperEquiv N q').symm (Additive.toMul x)) :
      heckeUpper N q') : Gamma0 N) = _
  rw [MulEquiv.apply_symm_apply]

private theorem hentry11 [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ y : Additive (Gamma0 N) →+ ℤ, BETA1 N q' (RES1 N q' y) = ((q' : ℤ) + 1) • y := by
  intro y
  show coresHom (heckeUpper N q')
      (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom) (pullbackHom (Ihara.ι₁ N q') y)) = _
  rw [pullback_symm_pullback_iota1]
  refine AddMonoidHom.ext fun g => ?_
  have h := coresHom_resHom_apply (heckeUpper N q') y (Additive.toMul g)
  rw [ModularCurve.index_heckeUpper hq' hq'N] at h
  change coresHom (heckeUpper N q') (resHom (heckeUpper N q') y) g = (q' + 1) • y g at h
  show coresHom (heckeUpper N q') (resHom (heckeUpper N q') y) g = ((q' : ℤ) + 1) • y g
  rw [h, nsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

private theorem hentry00 [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ y : Additive (Gamma0 N) →+ ℤ, BETA0 N q' hq' hq'N (RES0 N q' y) = ((q' : ℤ) + 1) • y := by
  intro y
  show degeneracyTransfer₀ N q' ℤ hq' hq'N (pullbackHom (Ihara.ι₀ N q') y) = _
  rw [degeneracyTransfer₀_apply, INHX2.degeneracyTransfer₀Aux_res0_eq_degeneracyTransfer₁_res1]
  exact hentry11 hq' hq'N y

end Plumbing
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

section W5J0weld
open scoped MatrixGroups

namespace W5J0

variable (N q' : ℕ) [NeZero N] [NeZero q']

omit [NeZero N] [NeZero q'] in

private theorem iotaDeg0_one_eq_iota0 (γ : Gamma0 (N * q')) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _) γ
      = Ihara.ι₀ N q' γ := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show ModularCurve.PDPairing.conjLowerMat 1 (γ : SL(2, ℤ))
        (ModularCurve.PDPairing.dvd_entry0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _) γ) i j
      = (((Ihara.ι₀ N q' γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
  have hι : (((Ihara.ι₀ N q' γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [hι]
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjLowerMat]

omit [NeZero N] [NeZero q'] in

private theorem range_iotaDeg0_one :
    (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _)).range
      = (Ihara.ι₀ N q').range := by
  ext x
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, (iotaDeg0_one_eq_iota0 N q' γ).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, iotaDeg0_one_eq_iota0 N q' γ⟩

omit [NeZero N] in

private theorem heckeUpper_comap_conj_bezout (a b : ℤ) (hab : (q' : ℤ) * a - (N : ℤ) * b = 1) :
    (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (Ihara.ι₀ N q').range := by
  ext x
  constructor
  · intro hx
    have hmem : bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹
        ∈ heckeUpper N q' := hx
    rw [← range_iota1 N (NeZero.ne q')] at hmem
    obtain ⟨δ, hδ⟩ := hmem
    have hsolve : alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) = δ := by
      rw [alConjHom_bezout_sq N q' a b hab]
      group
    have hι₁ : Ihara.ι₁ N q' δ
        = bezoutConjugator N q' a b hab *
            Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)
              ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
            (bezoutConjugator N q' a b hab)⁻¹ := by
      conv_lhs => rw [← hsolve]
      rw [iota1_alConjHom]
    refine ⟨alConjHom N q' (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab)
      ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab), ?_⟩
    have hux : bezoutConjugator N q' a b hab *
        Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
        (bezoutConjugator N q' a b hab)⁻¹
        = bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹ := by
      rw [← hι₁, hδ]
    exact mul_left_cancel (mul_right_cancel hux)
  · rintro ⟨γ, rfl⟩
    show bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
        (bezoutConjugator N q' a b hab)⁻¹ ∈ heckeUpper N q'
    exact (mem_heckeUpper N q').mpr (bezoutConjugator_heckeUpper_dvd N q' a b hab γ)

private theorem jDeg0_one_eq_degeneracyTransfer₀Aux (a b : ℤ)
    (hab : (q' : ℤ) * a - (N : ℤ) * b = 1)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x := by
  classical

  have hB0 : ∀ (K : Subgroup (Gamma0 N)) [K.FiniteIndex] (χ : Additive ↥K →+ ℤ),
      ModularCurve.PDPairing.coresAdd K χ = coresHom K χ := by
    intro K _ χ
    rw [coresHom_eq_transfer]
    rfl
  have hcomap : (heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range := by
    rw [heckeUpper_comap_conj_bezout N q' a b hab, range_iotaDeg0_one]
  haveI hFIcomap : ((heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom).FiniteIndex := by
    rw [hcomap]
    exact ModularCurve.PDPairing.iotaDeg0_range_finiteIndex _ _ _ _ _
  have hσsurj : Function.Surjective
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom :=
    (MulAut.conj (bezoutConjugator N q' a b hab)).surjective

  have hLHS : ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ
      (dvd_mul_right N q') (one_dvd _) φ x
      = coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range
          (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
            (dvd_mul_right N q') (one_dvd _) φ) x := by
    show ModularCurve.PDPairing.coresAdd _ _ x = _
    rw [hB0]
  have hRHS : degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x
      = coresHom (heckeUpper N q')
          (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
            (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)) x := rfl

  have hwash : coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
      (dvd_mul_right N q') (one_dvd _)).range
      (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
        (dvd_mul_right N q') (one_dvd _) φ) x
      = coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range
          (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
            (dvd_mul_right N q') (one_dvd _) φ)
          (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
            bezoutConjugator N q' a b hab)) := by
    rw [show Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
        bezoutConjugator N q' a b hab)
      = Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ : Gamma0 N)
        + Additive.ofMul (Additive.toMul x)
        + Additive.ofMul (bezoutConjugator N q' a b hab : Gamma0 N) from rfl]
    rw [map_add, map_add, ofMul_inv, map_neg]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx]
    abel

  have hG2 := INHX2.coresHom_comp_apply (heckeUpper N q')
    (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
    (INHX2.surj_quotMap_of_surjective _ _ hσsurj)
    (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ))
    ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)

  have hσg : (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)
      = Additive.toMul x := by
    show bezoutConjugator N q' a b hab *
        ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab) *
        (bezoutConjugator N q' a b hab)⁻¹ = Additive.toMul x
    group

  have hχ : ∀ (w : Gamma0 N)
      (h₁ : w ∈ (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)
      (h₂ : w ∈ (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
        (dvd_mul_right N q') (one_dvd _)).range),
      ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
        (AddMonoidHom.mk' (fun j => Additive.ofMul
          (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              (Additive.toMul j : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
            (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
        (Additive.ofMul ⟨w, h₁⟩)
      = (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
          (dvd_mul_right N q') (one_dvd _) φ) (Additive.ofMul ⟨w, h₂⟩) := by
    intro w h₁ h₂
    have hwK : w ∈ (Ihara.ι₀ N q').range := by
      rw [← range_iotaDeg0_one N q']
      exact h₂
    obtain ⟨γ, hγ⟩ := hwK

    have hval : (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
        h₁⟩ : ↥(heckeUpper N q'))
        = iotaUpperHom N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ) := by
      refine Subtype.ext ?_
      rw [coe_iotaUpperHom, iota1_alConjHom]
      show bezoutConjugator N q' a b hab * w * (bezoutConjugator N q' a b hab)⁻¹
          = bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
            (bezoutConjugator N q' a b hab)⁻¹
      rw [hγ]
    have hsymmcollapse : ∀ z : Gamma0 (N * q'),
        (iotaUpperEquiv N q').symm.toMonoidHom (iotaUpperHom N q' z) = z := by
      intro z
      show (iotaUpperEquiv N q').symm (iotaUpperHom N q' z) = z
      rw [← iotaUpperEquiv_apply, MulEquiv.symm_apply_apply]

    have hL : ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
        (AddMonoidHom.mk' (fun j => Additive.ofMul
          (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              (Additive.toMul j : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
            (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
        (Additive.ofMul ⟨w, h₁⟩)
        = φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab)
            (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ))) := by
      show (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
          (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ))
          (Additive.ofMul (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
            h₁⟩ : ↥(heckeUpper N q'))) = _
      rw [hval, pullbackHom_apply, hsymmcollapse, pullbackHom_apply]
    have hsq : φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ)))
        = φ (Additive.ofMul γ) := by
      rw [alConjHom_bezout_sq N q' a b hab]
      rw [show Additive.ofMul (alConjSqElt N q' a b hab * γ * (alConjSqElt N q' a b hab)⁻¹)
          = Additive.ofMul (alConjSqElt N q' a b hab) + Additive.ofMul γ
            + Additive.ofMul ((alConjSqElt N q' a b hab))⁻¹ from rfl]
      rw [map_add, map_add, ofMul_inv, map_neg]
      abel
    have hR : (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
        (dvd_mul_right N q') (one_dvd _) φ) (Additive.ofMul ⟨w, h₂⟩)
        = φ (Additive.ofMul γ) := by
      have hj : (⟨w, h₂⟩ : ↥(ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range)
          = (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
              (dvd_mul_right N q') (one_dvd _)).ofInjective
              (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
                (dvd_mul_right N q') (one_dvd _)) γ := by
        refine Subtype.ext ?_
        rw [MonoidHom.ofInjective_apply]
        show w = ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _) γ
        rw [iotaDeg0_one_eq_iota0, hγ]
      rw [hj]
      show φ (Additive.ofMul ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
          (dvd_mul_right N q') (one_dvd _))).symm
        ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
          (dvd_mul_right N q') (one_dvd _))) γ))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hL, hsq, hR]

  have hcongr := INHX2.coresHom_congr hcomap.symm
    (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
      (dvd_mul_right N q') (one_dvd _) φ)
    ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
      (AddMonoidHom.mk' (fun j => Additive.ofMul
        (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
            (Additive.toMul j : ↥((heckeUpper N q').comap
              (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
          (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
        (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
    (fun g hg => (hχ g (hcomap.symm ▸ hg) hg).symm)
    (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
      bezoutConjugator N q' a b hab))
  refine hLHS.trans (hwash.trans (hcongr.trans (hG2.symm.trans ?_)))
  have harg : Additive.ofMul ((MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab))
      = x := by
    rw [hσg]
    rfl
  rw [harg]
  exact hRHS.symm

private theorem jDeg0_one_eq_degeneracyTransfer₀ (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀ N q' ℤ hq' hq'N φ x :=
  jDeg0_one_eq_degeneracyTransfer₀Aux N q'
    (Int.gcdA (q' : ℤ) (N : ℤ)) (-Int.gcdB (q' : ℤ) (N : ℤ))
    (bezout_of_prime_not_dvd N q' hq' hq'N) φ x

end W5J0
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

end W5J0weld
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

section PDDock
open scoped MatrixGroups

variable {N q' : ℕ}

private theorem q_dvd_mul_div (N q : ℕ) : q ∣ (N * q) / N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [Nat.mul_div_cancel_left q h]

private theorem iotaDeg0_one_eq_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _) γ = Ihara.ι₀ N q γ := by
  refine Subtype.ext (Subtype.ext ?_)
  show (ModularCurve.PDPairing.conjLowerMat 1 ((γ : SL(2, ℤ)))
      (ModularCurve.PDPairing.dvd_entry0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _) γ)
      : Matrix (Fin 2) (Fin 2) ℤ)
    = (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjLowerMat]

private theorem iotaDeg0_q_eq_iota1 (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q) γ
      = Ihara.ι₁ N q γ :=
  Subtype.ext (Subtype.ext rfl)

private theorem iDeg0_one_eq_pullbackHom_iota0 (N q : ℕ) (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 N) →+ A) :
    ModularCurve.PDPairing.iDeg0 N (N * q) 1 ℤ A (dvd_mul_right N q) (one_dvd _) φ
      = pullbackHom (Ihara.ι₀ N q) φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _)
      (Additive.toMul x)))
    = φ (Additive.ofMul (Ihara.ι₀ N q (Additive.toMul x)))
  rw [iotaDeg0_one_eq_iota0]

private theorem iDeg0_q_eq_pullbackHom_iota1 (N q : ℕ) (A : Type*) [AddCommGroup A] [NeZero q]
    (φ : Additive (Gamma0 N) →+ A) :
    ModularCurve.PDPairing.iDeg0 N (N * q) q ℤ A (dvd_mul_right N q) (q_dvd_mul_div N q) φ
      = pullbackHom (Ihara.ι₁ N q) φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)
      (Additive.toMul x)))
    = φ (Additive.ofMul (Ihara.ι₁ N q (Additive.toMul x)))
  rw [iotaDeg0_q_eq_iota1]

private theorem coresAdd_eq_coresHom {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex]
    {A : Type*} [AddCommGroup A] (ψ : Additive ↥K →+ A) :
    ModularCurve.PDPairing.coresAdd K ψ = coresHom K ψ := by
  rw [HeckeEis.coresHom_eq_transfer]
  rfl

private theorem range_iotaDeg0_q (N q : ℕ) [NeZero q] :
    (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)).range
      = heckeUpper N q := by
  have h1 : (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)).range
      = (Ihara.ι₁ N q).range := by
    refine Subgroup.ext fun γ => ⟨?_, ?_⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, (iotaDeg0_q_eq_iota1 N q δ).symm⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, iotaDeg0_q_eq_iota1 N q δ⟩
  rw [h1, range_iota1 N (NeZero.ne q)]

private theorem jDeg0_q_eq_degeneracyTransfer₁_apply (N q : ℕ) [NeZero (N * q)] [NeZero q]
    (A : Type*) [AddCommGroup A]
    (ψ : Additive (Gamma0 (N * q)) →+ A) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q) q ℤ A (dvd_mul_right N q) (q_dvd_mul_div N q) ψ x
      = degeneracyTransfer₁ N q A ψ x := by
  show ModularCurve.PDPairing.coresAdd _
      (ModularCurve.PDPairing.pushChar0 N (N * q) q A (dvd_mul_right N q) (q_dvd_mul_div N q) ψ) x
    = degeneracyTransfer₁ N q A ψ x
  rw [coresAdd_eq_coresHom]
  show _ = coresHom (heckeUpper N q)
      (pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom) ψ) x
  refine INHX2.coresHom_congr (range_iotaDeg0_q N q) _ _ (fun g h₁ => ?_) x
  show ψ (Additive.ofMul (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩))
    = ψ (Additive.ofMul ((iotaUpperEquiv N q).symm
        ⟨g, (range_iotaDeg0_q N q) ▸ h₁⟩))
  refine congrArg ψ (congrArg Additive.ofMul ?_)
  have e₁ : Ihara.ι₁ N q (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩) = g := by
    have h := MulEquiv.apply_symm_apply ((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))) ⟨g, h₁⟩
    have hval : ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)
        (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
          (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
          (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩) = g :=
      congrArg Subtype.val h
    rw [iotaDeg0_q_eq_iota1] at hval
    exact hval
  have e₂ : Ihara.ι₁ N q ((iotaUpperEquiv N q).symm
      ⟨g, (range_iotaDeg0_q N q) ▸ h₁⟩) = g :=
    congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply _)
  have hinj : Function.Injective (Ihara.ι₁ N q) := fun a b hab =>
    (iotaUpperEquiv N q).injective (Subtype.ext hab)
  exact hinj (e₁.trans e₂.symm)

private theorem gamma0HUpper_eq_heckeUpper (M ℓ : ℕ) :
    ModularCurve.PDPairing.Gamma0HUpper M ℓ = heckeUpper M ℓ := by
  refine Subgroup.ext fun γ => ?_
  rw [mem_heckeUpper]
  constructor
  · intro h
    exact ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper M ℓ ⟨γ, h⟩
  · intro h
    exact Subgroup.mem_subgroupOf.mpr (ModularCurve.PDPairing.mem_Gamma0Upper.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))

private theorem heckeT0_eq_heckeOperatorHom_apply (M ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 M) →+ A) (x : Additive (Gamma0 M)) :
    ModularCurve.PDPairing.heckeT0 M ℓ A φ x = heckeOperatorHom M ℓ A φ x := by
  have hL : ModularCurve.PDPairing.heckeT0 M ℓ A φ x
      = coresHom (ModularCurve.PDPairing.Gamma0HUpper M ℓ)
          (φ.comp (MonoidHom.toAdditive (ModularCurve.PDPairing.conjL0 M ℓ))) x := by
    have hcores := HeckeEis.coresHom_eq_transfer (H := ModularCurve.PDPairing.Gamma0HUpper M ℓ)
      (φ.comp (MonoidHom.toAdditive (ModularCurve.PDPairing.conjL0 M ℓ)))
    rw [hcores]
    rfl
  rw [hL]
  show _ = coresHom (heckeUpper M ℓ) (pullbackHom (heckeConj M ℓ) φ) x
  refine INHX2.coresHom_congr (gamma0HUpper_eq_heckeUpper M ℓ) _ _ (fun g h₁ => ?_) x
  exact congrArg φ (congrArg Additive.ofMul (Subtype.ext (Subtype.ext rfl)))

private theorem W5j0 (N q' : ℕ) [NeZero N] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    haveI : NeZero (N * q') := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q')⟩
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀ N q' ℤ hq' hq'N φ x :=
  W5J0.jDeg0_one_eq_degeneracyTransfer₀ N q' hq' hq'N φ x

private theorem PDpairing5 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N q' : ℕ) [NeZero N] [NeZero q'] (hq' : q'.Prime)
    (hq'N : ¬ q' ∣ N) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, (p : ℤ) ∣ pair₁ x y) → ∃ x', x = (p : ℤ) • x') ∧
        (∀ y, (∀ x, (p : ℤ) ∣ pair₁ x y) → ∃ y', y = (p : ℤ) • y')) ∧
      ((∀ x, (∀ y, (p : ℤ) ∣ pair₀ x y) → ∃ x', x = (p : ℤ) • x') ∧
        (∀ y, (∀ x, (p : ℤ) ∣ pair₀ x y) → ∃ y', y = (p : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
          pair₁ ⟨heckeOperatorHom (N * q') ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ x x.2⟩ y =
            pair₁ x ⟨heckeOperatorHom (N * q') ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨heckeOperatorHom N ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ x x.2⟩ y =
            pair₀ x ⟨heckeOperatorHom N ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA0 N q' hq' hq'N x, INHX2.isParabolicHom_degeneracyTransfer₀Aux _ _ x.2⟩ y =
            pair₁ x ⟨RES0 N q' y, INHX2.isParabolicHom_pullback_iota0 y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA1 N q' x, INHX2.isParabolicHom_degeneracyTransfer₁ x.2⟩ y =
            pair₁ x ⟨RES1 N q' y, INHX2.isParabolicHom_pullback_iota1 y.2⟩) := by
  haveI : IsFreeGroup ↥(Gamma 4) := ModularCurve.PDPairing.isFreeGroup_Gamma_four
  haveI : NeZero (N * q') := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q')⟩
  have hT : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
      heckeOperatorHom M ℓ ℤ φ = ModularCurve.PDPairing.heckeT0 M ℓ ℤ φ :=
    fun M ℓ _ φ => AddMonoidHom.ext fun g => (heckeT0_eq_heckeOperatorHom_apply M ℓ ℤ φ g).symm
  refine ⟨ModularCurve.PDPairing.pairZ (N * q'), ModularCurve.PDPairing.pairZ N,
    ModularCurve.PDPairing.pairZ_nondegenerate_mod (N * q') p hp hp5,
    ModularCurve.PDPairing.pairZ_nondegenerate_mod N p hp hp5, ?_, ?_, ?_, ?_⟩
  · intro ℓ _ hℓ hℓNq x y
    show ModularCurve.PDPairing.pairZFun (N * q') (heckeOperatorHom (N * q') ℓ ℤ x) y
      = ModularCurve.PDPairing.pairZFun (N * q') x (heckeOperatorHom (N * q') ℓ ℤ y)
    rw [hT, hT]
    exact ModularCurve.PDPairing.pairZFun_heckeT0_comm (N * q') ℓ hℓ hℓNq x y x.2 y.2
  · intro ℓ _ hℓ hℓNq x y
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (Dvd.dvd.mul_right h q')
    show ModularCurve.PDPairing.pairZFun N (heckeOperatorHom N ℓ ℤ x) y
      = ModularCurve.PDPairing.pairZFun N x (heckeOperatorHom N ℓ ℤ y)
    rw [hT, hT]
    exact ModularCurve.PDPairing.pairZFun_heckeT0_comm N ℓ hℓ hℓN x y x.2 y.2
  · intro x y
    show ModularCurve.PDPairing.pairZFun N (BETA0 N q' hq' hq'N x) y
      = ModularCurve.PDPairing.pairZFun (N * q') x (RES0 N q' y)
    have hj : BETA0 N q' hq' hq'N (x : Additive (Gamma0 (N * q')) →+ ℤ)
        = ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) x :=
      AddMonoidHom.ext fun g => (W5j0 N q' hq' hq'N x g).symm
    have hi : RES0 N q' (y : Additive (Gamma0 N) →+ ℤ)
        = ModularCurve.PDPairing.iDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) y :=
      (iDeg0_one_eq_pullbackHom_iota0 N q' ℤ y).symm
    rw [hj, hi]
    exact ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _) x y x.2 y.2
  · intro x y
    show ModularCurve.PDPairing.pairZFun N (BETA1 N q' x) y
      = ModularCurve.PDPairing.pairZFun (N * q') x (RES1 N q' y)
    have hj : BETA1 N q' (x : Additive (Gamma0 (N * q')) →+ ℤ)
        = ModularCurve.PDPairing.jDeg0 N (N * q') q' ℤ ℤ (dvd_mul_right N q') (q_dvd_mul_div N q') x :=
      AddMonoidHom.ext fun g => (jDeg0_q_eq_degeneracyTransfer₁_apply N q' ℤ x g).symm
    have hi : RES1 N q' (y : Additive (Gamma0 N) →+ ℤ)
        = ModularCurve.PDPairing.iDeg0 N (N * q') q' ℤ ℤ (dvd_mul_right N q') (q_dvd_mul_div N q') y :=
      (iDeg0_q_eq_pullbackHom_iota1 N q' ℤ y).symm
    rw [hj, hi]
    exact ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q') q' (dvd_mul_right N q') (q_dvd_mul_div N q') x y
      x.2 y.2

private theorem PDpairing3 (N q' : ℕ) [NeZero N] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, ((3 : ℕ) : ℤ) ∣ pair₁ x y) → ∃ x', x = ((3 : ℕ) : ℤ) • x') ∧
        (∀ y, (∀ x, ((3 : ℕ) : ℤ) ∣ pair₁ x y) → ∃ y', y = ((3 : ℕ) : ℤ) • y')) ∧
      ((∀ x, (∀ y, ((3 : ℕ) : ℤ) ∣ pair₀ x y) → ∃ x', x = ((3 : ℕ) : ℤ) • x') ∧
        (∀ y, (∀ x, ((3 : ℕ) : ℤ) ∣ pair₀ x y) → ∃ y', y = ((3 : ℕ) : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
          pair₁ ⟨heckeOperatorHom (N * q') ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ x x.2⟩ y =
            pair₁ x ⟨heckeOperatorHom (N * q') ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨heckeOperatorHom N ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ x x.2⟩ y =
            pair₀ x ⟨heckeOperatorHom N ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA0 N q' hq' hq'N x, INHX2.isParabolicHom_degeneracyTransfer₀Aux _ _ x.2⟩ y =
            pair₁ x ⟨RES0 N q' y, INHX2.isParabolicHom_pullback_iota0 y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA1 N q' x, INHX2.isParabolicHom_degeneracyTransfer₁ x.2⟩ y =
            pair₁ x ⟨RES1 N q' y, INHX2.isParabolicHom_pullback_iota1 y.2⟩) := by
  obtain ⟨pair₁, pair₀, hperf₁, hperf₀, hadj₁, hadj₀, hproj₀, hproj₁⟩ :=
    LevelRaising.exists_parabolicPairings_perfect_mod_three N q' hq' hq'N hTpar_int
      (hrespar0 (N := N) (q' := q')) (hrespar1 (N := N) (q' := q')) (hbetapar0 hq' hq'N) hbetapar1
  refine ⟨pair₁, pair₀, ?_, ?_, hadj₁, hadj₀, hproj₀, hproj₁⟩
  · simpa only [Nat.cast_ofNat] using hperf₁
  · simpa only [Nat.cast_ofNat] using hperf₀

private theorem PDpairing_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N q' : ℕ) [NeZero N] [NeZero q'] (hq' : q'.Prime)
    (hq'N : ¬ q' ∣ N) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, (p : ℤ) ∣ pair₁ x y) → ∃ x', x = (p : ℤ) • x') ∧
        (∀ y, (∀ x, (p : ℤ) ∣ pair₁ x y) → ∃ y', y = (p : ℤ) • y')) ∧
      ((∀ x, (∀ y, (p : ℤ) ∣ pair₀ x y) → ∃ x', x = (p : ℤ) • x') ∧
        (∀ y, (∀ x, (p : ℤ) ∣ pair₀ x y) → ∃ y', y = (p : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
          pair₁ ⟨heckeOperatorHom (N * q') ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ x x.2⟩ y =
            pair₁ x ⟨heckeOperatorHom (N * q') ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * q') ℓ ℤ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨heckeOperatorHom N ℓ ℤ x,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ x x.2⟩ y =
            pair₀ x ⟨heckeOperatorHom N ℓ ℤ y,
              ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA0 N q' hq' hq'N x, INHX2.isParabolicHom_degeneracyTransfer₀Aux _ _ x.2⟩ y =
            pair₁ x ⟨RES0 N q' y, INHX2.isParabolicHom_pullback_iota0 y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨BETA1 N q' x, INHX2.isParabolicHom_degeneracyTransfer₁ x.2⟩ y =
            pair₁ x ⟨RES1 N q' y, INHX2.isParabolicHom_pullback_iota1 y.2⟩) := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have hp3 : p = 3 := by
      have h2le := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · rcases hp.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩ with h | h <;> omega
    subst hp3
    exact PDpairing3 N q' hq' hq'N
  · exact PDpairing5 p hp h5 N q' hq' hq'N

end PDDock
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

section Corloc

variable {N q' : ℕ}

private theorem exists_eq_smul_of_forall_dvd {G : Type*} [AddZeroClass G] {p : ℕ} (hp : p ≠ 0)
    (θ : G →+ ℤ) (h : ∀ g, (p : ℤ) ∣ θ g) : ∃ θ' : G →+ ℤ, θ = (p : ℤ) • θ' := by
  have hp' : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp
  refine ⟨{ toFun := fun g => θ g / p, map_zero' := by simp, map_add' := ?_ }, ?_⟩
  · intro g g'
    obtain ⟨c, hc⟩ := h g
    obtain ⟨c', hc'⟩ := h g'
    show θ (g + g') / p = θ g / p + θ g' / p
    rw [map_add, hc, hc', ← mul_add, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp',
      Int.mul_ediv_cancel_left _ hp']
  · refine AddMonoidHom.ext fun g => ?_
    obtain ⟨c, hc⟩ := h g
    show θ g = (p : ℤ) • (θ g / p)
    rw [hc, Int.mul_ediv_cancel_left _ hp', zsmul_eq_mul, Int.cast_id]

private theorem dvd_of_castAddHom_comp_eq_zero {G : Type*} [AddZeroClass G] {p : ℕ}
    (θ : G →+ ℤ) (h : (Int.castAddHom (ZMod p)).comp θ = 0) (g : G) : (p : ℤ) ∣ θ g := by
  have := DFunLike.congr_fun h g
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

private theorem corloc5 (p : ℕ) (hpp : p.Prime) (hp5 : 5 ≤ p) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, RES0 N q' φ + RES1 N q' ψ = (p : ℤ) • χ) →
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (p : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (p : ℤ) • ψ') := by
  intro φ ψ hχ ℓ _ hℓ hℓNq
  obtain ⟨χ, hχ⟩ := hχ
  have hp : p.Prime := hpp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (Dvd.dvd.mul_right h q')

  set φb : Additive (Gamma0 N) →+ ZMod p := (Int.castAddHom (ZMod p)).comp φ with hφb
  set ψb : Additive (Gamma0 N) →+ ZMod p := (Int.castAddHom (ZMod p)).comp ψ with hψb

  have hne : ∀ m : ℕ, 0 < m → m < 5 → (m : ZMod p) ≠ 0 := by
    intro m hm hm5 h0
    have hdvd := (ZMod.natCast_eq_zero_iff m p).mp h0
    have := Nat.le_of_dvd hm hdvd
    have := hp5
    omega
  have h2 : ∀ a : ZMod p, a + a = 0 → a = 0 := by
    intro a ha
    have h2' : (2 : ZMod p) * a = 0 := by rw [two_mul]; exact ha
    rcases mul_eq_zero.mp h2' with h | h
    · exact absurd (by exact_mod_cast h) (hne 2 (by norm_num) (by norm_num))
    · exact h
  have h3 : ∀ a : ZMod p, a + a + a = 0 → a = 0 := by
    intro a ha
    have h3' : (3 : ZMod p) * a = 0 := by
      rw [show (3 : ZMod p) * a = a + a + a by ring]; exact ha
    rcases mul_eq_zero.mp h3' with h | h
    · exact absurd (by exact_mod_cast h) (hne 3 (by norm_num) (by norm_num))
    · exact h

  have hker : ∀ γ : Gamma0 (N * q'), φb (Ihara.ι₀ N q' γ) + ψb (Ihara.ι₁ N q' γ) = 0 := by
    intro γ
    have hγ := DFunLike.congr_fun hχ (Additive.ofMul γ)
    change φ (Additive.ofMul (Ihara.ι₀ N q' γ)) + ψ (Additive.ofMul (Ihara.ι₁ N q' γ)) =
      (p : ℤ) • χ (Additive.ofMul γ) at hγ
    show ((φ (Additive.ofMul (Ihara.ι₀ N q' γ)) : ℤ) : ZMod p) +
      ((ψ (Additive.ofMul (Ihara.ι₁ N q' γ)) : ℤ) : ZMod p) = 0
    rw [← Int.cast_add, hγ, zsmul_eq_mul, Int.cast_mul]
    simp
  have hB := heckeOperatorHom_eq_of_levelRaisingKernel N q' hq' hq'N (ZMod p) h2 h3 φb ψb hker hℓ hℓN

  have lift : ∀ θ : Additive (Gamma0 N) →+ ℤ,
      heckeOperatorHom N ℓ (ZMod p) ((Int.castAddHom (ZMod p)).comp θ) =
        (ℓ + 1) • (Int.castAddHom (ZMod p)).comp θ →
      ∃ θ' : Additive (Gamma0 N) →+ ℤ,
        heckeOperatorHom N ℓ ℤ θ - ((ℓ : ℤ) + 1) • θ = (p : ℤ) • θ' := by
    intro θ hθ
    refine exists_eq_smul_of_forall_dvd hp0 _ fun g => ?_
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hnat := DFunLike.congr_fun (postcomp_heckeOperatorHom N ℓ (Int.castAddHom (ZMod p)) θ) g
    have hθg := DFunLike.congr_fun hθ g
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom] at hnat
    rw [AddMonoidHom.sub_apply, Int.cast_sub]
    rw [show ((((ℓ : ℤ) + 1) • θ) g : ℤ) = ((ℓ : ℤ) + 1) * θ g from rfl]
    rw [hnat, hθg]
    rw [show (((ℓ + 1) • ((Int.castAddHom (ZMod p)).comp θ)) g) =
      (ℓ + 1) • (((θ g : ℤ)) : ZMod p) from rfl]
    rw [nsmul_eq_mul]
    push_cast
    ring
  exact ⟨lift φ hB.1, lift ψ hB.2⟩

private theorem corloc3 (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, RES0 N q' φ + RES1 N q' ψ = ((3 : ℕ) : ℤ) • χ) →
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = ((3 : ℕ) : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = ((3 : ℕ) : ℤ) • ψ') := by
  intro φ ψ hφ hψ hχ ℓ _ hℓ hℓM
  obtain ⟨χ, hχ⟩ := hχ
  have hker : ∀ γ : Gamma0 (N * q'), (3 : ℤ) ∣ φ (Ihara.ι₀ N q' γ) + ψ (Ihara.ι₁ N q' γ) := by
    intro γ
    have hγ := DFunLike.congr_fun hχ (Additive.ofMul γ)
    change φ (Additive.ofMul (Ihara.ι₀ N q' γ)) + ψ (Additive.ofMul (Ihara.ι₁ N q' γ)) =
      ((3 : ℕ) : ℤ) • χ (Additive.ofMul γ) at hγ
    refine ⟨χ (Additive.ofMul γ), ?_⟩
    change φ (Additive.ofMul (Ihara.ι₀ N q' γ)) + ψ (Additive.ofMul (Ihara.ι₁ N q' γ)) = 3 * χ (Additive.ofMul γ)
    rw [hγ, zsmul_eq_mul]
    push_cast
    ring
  have h := Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel N q' hq' hq'N φ ψ hφ hψ
    hker hℓ hℓM
  simpa only [Nat.cast_ofNat] using h

private theorem corloc_odd (p : ℕ) (hpp : p.Prime) (hp2 : p ≠ 2) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, RES0 N q' φ + RES1 N q' ψ = (p : ℤ) • χ) →
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (p : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ,
          heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (p : ℤ) • ψ') := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have hp3 : p = 3 := by
      have h2le := hpp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · rcases hpp.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩ with h | h <;> omega
    subst hp3
    exact corloc3 hq' hq'N
  · intro φ ψ _ _ hχ ℓ _ hℓ hℓM
    exact corloc5 p hpp h5 hq' hq'N φ ψ hχ ℓ hℓ hℓM

end Corloc
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

namespace Tau

private theorem intCast_mem_iff (p : ℕ) [hp : Fact p.Prime] {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) (x : ℤ) :
    ((x : integralClosure ℤ ℂ) ∈ 𝔪) ↔ (p : ℤ) ∣ x := by
  constructor
  · intro hx𝔪
    by_contra hpx
    have hcop : IsCoprime (p : ℤ) x :=
      ((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd).mpr hpx
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : (1 : integralClosure ℤ ℂ) ∈ 𝔪 := by
      have hcast : ((u : ℤ) : integralClosure ℤ ℂ) * ((p : ℤ) : integralClosure ℤ ℂ)
          + ((v : ℤ) : integralClosure ℤ ℂ) * ((x : ℤ) : integralClosure ℤ ℂ) = 1 := by
        exact_mod_cast congrArg (fun t : ℤ => (t : integralClosure ℤ ℂ)) huv
      rw [← hcast]
      exact 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ hx𝔪)
    exact h𝔪.ne_top (𝔪.eq_top_of_isUnit_mem h1 isUnit_one)
  · rintro ⟨k, rfl⟩
    push_cast
    exact 𝔪.mul_mem_right _ hp𝔪

private theorem charP_quotient (p : ℕ) [Fact p.Prime] {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    CharP (integralClosure ℤ ℂ ⧸ 𝔪) p := by
  refine ⟨fun k => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk 𝔪) k, Ideal.Quotient.eq_zero_iff_mem]
  have := intCast_mem_iff p h𝔪 hp𝔪 (k : ℤ)
  simp only [Int.cast_natCast] at this
  rw [this]
  exact Int.natCast_dvd_natCast

private theorem exists_poly (p : ℕ) [Fact p.Prime] {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) (α : integralClosure ℤ ℂ) (n : ℤ)
    (hαn : α - (n : integralClosure ℤ ℂ) ∉ 𝔪) :
    ∃ m : Polynomial ℤ, Polynomial.aeval α m ∈ 𝔪 ∧ ((m.eval n : ℤ) : ZMod p) ≠ 0 := by
  classical
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  haveI : CharP (integralClosure ℤ ℂ ⧸ 𝔪) p := charP_quotient p h𝔪 hp𝔪
  letI : Algebra (ZMod p) (integralClosure ℤ ℂ ⧸ 𝔪) := ZMod.algebra _ p

  have hint_ℤ : IsIntegral ℤ (Ideal.Quotient.mkₐ ℤ 𝔪 α) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ) α).map (Ideal.Quotient.mkₐ ℤ 𝔪)
  have hint : IsIntegral (ZMod p) (Ideal.Quotient.mkₐ ℤ 𝔪 α) := by
    obtain ⟨f, hfm, hf⟩ := hint_ℤ
    refine ⟨f.map (Int.castRingHom (ZMod p)), hfm.map (Int.castRingHom (ZMod p)), ?_⟩
    rw [Polynomial.eval₂_map]
    convert hf using 2 <;> first | rfl | exact RingHom.ext_int _ _ | exact Subsingleton.elim _ _

  obtain ⟨m, hm⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective
    (minpoly (ZMod p) (Ideal.Quotient.mkₐ ℤ 𝔪 α))
  refine ⟨m, ?_, ?_⟩
  ·
    have h1 : Ideal.Quotient.mkₐ ℤ 𝔪 (Polynomial.aeval α m) = Polynomial.aeval (Ideal.Quotient.mkₐ ℤ 𝔪 α) m :=
      (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ 𝔪) α m).symm
    have h2 : Polynomial.aeval (Ideal.Quotient.mkₐ ℤ 𝔪 α) m = 0 := by
      have h3 := minpoly.aeval (ZMod p) (Ideal.Quotient.mkₐ ℤ 𝔪 α)
      rw [← hm, Polynomial.aeval_def, Polynomial.eval₂_map] at h3
      rw [Polynomial.aeval_def]
      convert h3 using 2 <;> first | rfl | exact RingHom.ext_int _ _ | exact Subsingleton.elim _ _
    have h4 : Ideal.Quotient.mk 𝔪 (Polynomial.aeval α m) = 0 := h1.trans h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h4
  ·
    intro h0
    apply hαn
    have hroot : (minpoly (ZMod p) (Ideal.Quotient.mkₐ ℤ 𝔪 α)).IsRoot ((n : ℤ) : ZMod p) := by
      rw [← hm]
      show Polynomial.eval _ _ = 0
      rw [Polynomial.eval_intCast_map]
      simpa using h0
    have hαeq := minpoly.root hint hroot
    rw [map_intCast] at hαeq
    have h5 : Ideal.Quotient.mk 𝔪 α = Ideal.Quotient.mk 𝔪 (n : integralClosure ℤ ℂ) := by
      rw [map_intCast]
      exact hαeq.symm
    exact Ideal.Quotient.eq.mp h5

end Tau
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

end INH.D6
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

open CongruenceSubgroup HeckeEis INH.D6 in

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {N q' : ℕ} (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) [NeZero (N * q')]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : CuspForm.IsNormalizedEigenform f)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ)
    (hχ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
      ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff f ℓ)
    (aq : integralClosure ℤ ℂ) (haq : (aq : ℂ) = ModularFormClass.qCoeff f q')
    (hrais : aq ^ 2 - (((q' : ℤ) + 1) ^ 2 : ℤ) ∈ 𝔪)
    (hnEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'), ℓ ≠ p ∧
      χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) - (((ℓ : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ) ∉ 𝔪)
    (A : ModularForm.AtkinLehnerDatum (N * q') q') :
    ∀ T : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'},
      (∀ g ∈ LinearMap.ker (CuspForm.traceLin A hq')
            ⊓ LinearMap.ker ((CuspForm.traceLin A hq') ∘ₗ (CuspForm.atkinLehnerLin A 2)),
        (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * q')) 2)) g = 0) → T ∈ Ideal.comap χ₁ 𝔪 := by

  haveI hpf : Fact p.Prime := ⟨hp⟩
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : NeZero N := ⟨fun hN => NeZero.ne (N * q') (by rw [hN, zero_mul])⟩
  obtain ⟨ℓ₀, hℓ₀p, hℓ₀M, -, hℓ₀nEis⟩ := hnEis
  haveI : NeZero ℓ₀ := ⟨hℓ₀p.ne_zero⟩

  obtain ⟨r, ws, hws, hspan⟩ := LRf.Endgame.exists_words_span (N := N) (q' := q') χ₁ 𝔪

  obtain ⟨m, hmα, hme⟩ := INH.D6.Tau.exists_poly p h𝔪 hp𝔪 (χ₁ (CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M))
    ((ℓ₀ : ℤ) + 1) hℓ₀nEis
  obtain ⟨mw, hmw⟩ : ∃ mw : FreeAlgebra ℤ ℕ, mw = Polynomial.aeval (FreeAlgebra.ι ℤ ℓ₀) m := ⟨_, rfl⟩

  have hι : LRf.wordValue N q' (FreeAlgebra.ι ℤ ℓ₀) = CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M := by
    apply Subtype.ext
    rw [LRf.coe_wordValue, CuspForm.heckeWordForms_ι,
      CuspForm.heckeWordGenForms_of_not_dvd hℓ₀p hℓ₀M hℓ₀M]
    rfl
  have hmw_val : χ₁ (LRf.wordValue N q' mw) ∈ 𝔪 := by
    have h1 : LRf.wordValue N q' mw = Polynomial.aeval (CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M) m := by
      rw [hmw]
      exact (Polynomial.aeval_algHom_apply (LRf.wordValue N q') (FreeAlgebra.ι ℤ ℓ₀) m).symm.trans (by rw [hι])
    have h2 : χ₁ (Polynomial.aeval (CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M) m)
        = Polynomial.aeval (χ₁ (CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M)) m :=
      (Polynomial.aeval_algHom_apply χ₁.toIntAlgHom (CuspForm.heckeAlgebra.T hℓ₀p hℓ₀M hℓ₀M) m).symm
    rw [h1, h2]
    exact hmα

  obtain ⟨ws', hws'⟩ : ∃ ws' : ℕ → FreeAlgebra ℤ ℕ, ws' = fun i => if i < r then ws i else mw := ⟨_, rfl⟩
  have hws'_lt : ∀ i, i < r → ws' i = ws i := fun i hi => by rw [hws']; exact if_pos hi
  have hws'_r : ws' r = mw := by rw [hws']; exact if_neg (lt_irrefl r)
  have hws'_val : ∀ i, i < r + 1 → χ₁ (LRf.wordValue N q' (ws' i)) ∈ 𝔪 := by
    intro i hi
    by_cases h : i < r
    · rw [hws'_lt i h]; exact hws i h
    · have hir : i = r := by omega
      rw [hir, hws'_r]; exact hmw_val

  obtain ⟨c, hc𝔪, hc⟩ : ∃ c : ℤ, (c : integralClosure ℤ ℂ) - aq ∈ 𝔪 ∧ (p : ℤ) ∣ c ^ 2 - ((q' : ℤ) + 1) ^ 2 := by
    have hfac : (aq - (((q' : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ))
        * (aq + (((q' : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ)) ∈ 𝔪 := by
      have hmul : (aq - (((q' : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ))
          * (aq + (((q' : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ))
          = aq ^ 2 - (((q' : ℤ) + 1) ^ 2 : ℤ) := by push_cast; ring
      rw [hmul]; exact hrais
    rcases h𝔪.isPrime.mem_or_mem hfac with h | h
    · refine ⟨(q' : ℤ) + 1, ?_, ⟨0, by ring⟩⟩
      have hneg := 𝔪.neg_mem h
      rw [neg_sub] at hneg
      exact hneg
    · refine ⟨-((q' : ℤ) + 1), ?_, ⟨0, by ring⟩⟩
      have hneg := 𝔪.neg_mem h
      have heq : ((-((q' : ℤ) + 1) : ℤ) : integralClosure ℤ ℂ) - aq
          = -(aq + (((q' : ℤ) + 1 : ℤ) : integralClosure ℤ ℂ)) := by push_cast; ring
      rw [heq]; exact hneg

  obtain ⟨φ₀, hφ₀par, hφ₀ne, hφ₀W, hφ₀q'⟩ :=
    LRf.Seed.exists_seed hq' hf h𝔪 p hp𝔪 χ₁ hχ₁ aq haq c hc𝔪 (r + 1) ws' hws'_val

  obtain ⟨UN, hUN⟩ : ∃ UN : ℕ → ((Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ)),
      UN = fun i => (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i)).toAddMonoidHom := ⟨_, rfl⟩
  obtain ⟨UM, hUM⟩ : ∃ UM : ℕ → ((Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ)),
      UM = fun i => (HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} (ws i)).toAddMonoidHom := ⟨_, rfl⟩
  obtain ⟨τN, hτN⟩ : ∃ τN : (Additive (Gamma0 N) →+ ℤ) →+ (Additive (Gamma0 N) →+ ℤ),
      τN = (HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} mw).toAddMonoidHom := ⟨_, rfl⟩
  obtain ⟨τM, hτM⟩ : ∃ τM : (Additive (Gamma0 (N * q')) →+ ℤ) →+ (Additive (Gamma0 (N * q')) →+ ℤ),
      τM = (HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} mw).toAddMonoidHom := ⟨_, rfl⟩
  have hUN_apply : ∀ i x, UN i x = HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} (ws i) x := by
    intro i x; rw [hUN]; rfl
  have hUM_apply : ∀ i x, UM i x = HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} (ws i) x := by
    intro i x; rw [hUM]; rfl
  have hτN_apply : ∀ x, τN x = HeckeEis.heckeWordHom N ℤ {ℓ | ℓ ∣ N * q'} mw x := by
    intro x; rw [hτN]; rfl
  have hτM_apply : ∀ x, τM x = HeckeEis.heckeWordHom (N * q') ℤ {ℓ | ℓ ∣ N * q'} mw x := by
    intro x; rw [hτM]; rfl

  have hτN_aeval : ∀ x, τN x = Polynomial.aeval (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap m x := by
    intro x
    rw [hτN_apply, hmw, LRf.Words.heckeWordHom_aeval_ι N N q' hℓ₀p hℓ₀M m]
  have hτM_aeval : ∀ x,
      τM x = Polynomial.aeval (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap m x := by
    intro x
    rw [hτM_apply, hmw, LRf.Words.heckeWordHom_aeval_ι (N * q') N q' hℓ₀p hℓ₀M m]

  have hτNpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      τN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ := by
    intro x hx; rw [hτN_apply]; exact LRf.Words.heckeWordHom_mem_parabolicHoms N N q' mw x hx
  have hτMpar : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      τM x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ := by
    intro x hx; rw [hτM_apply]; exact LRf.Words.heckeWordHom_mem_parabolicHoms (N * q') N q' mw x hx
  have hUMpar : ∀ i, i < r → ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      UM i x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ := by
    intro i _ x hx; rw [hUM_apply]; exact LRf.Words.heckeWordHom_mem_parabolicHoms (N * q') N q' (ws i) x hx

  have hUcomm : ∀ i, i < r → ∀ x, UM i (τM x) = τM (UM i x) := by
    intro i _ x
    rw [hτM_aeval, hτM_aeval]
    exact LRf.Words.aeval_comm_of_comm (UM i) (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap
      (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap
      (fun y => by
        rw [hUM_apply, hUM_apply]
        exact LRf.Words.heckeWordHom_comm_heckeOperatorHom (N * q') N q' (ws i) hℓ₀p y) m x

  have hφ₀τ : ∃ ψ : Additive (Gamma0 N) →+ ℤ, τN φ₀ = (p : ℤ) • ψ := by
    obtain ⟨ψ, hψ⟩ := hφ₀W r (Nat.lt_succ_self r)
    rw [hws'_r] at hψ
    exact ⟨ψ, by rw [hτN_apply]; exact hψ⟩
  have hφ₀U : ∀ i, i < r → ∃ ψ : Additive (Gamma0 N) →+ ℤ, UN i φ₀ = (p : ℤ) • ψ := by
    intro i hi
    obtain ⟨ψ, hψ⟩ := hφ₀W i (Nat.lt_succ_of_lt hi)
    rw [hws'_lt i hi] at hψ
    exact ⟨ψ, by rw [hUN_apply]; exact hψ⟩

  have hresτ₀ : ∀ φ, RES0 N q' (τN φ) = τM (RES0 N q' φ) := by
    intro φ; rw [hτN_apply, hτM_apply]; exact LRf.Words.pullbackHom_iota0_heckeWordHom N q' mw φ
  have hresτ₁ : ∀ φ, RES1 N q' (τN φ) = τM (RES1 N q' φ) := by
    intro φ; rw [hτN_apply, hτM_apply]; exact LRf.Words.pullbackHom_iota1_heckeWordHom N q' mw φ
  have hresU₀ : ∀ i, i < r → ∀ φ, RES0 N q' (UN i φ) = UM i (RES0 N q' φ) := by
    intro i _ φ; rw [hUN_apply, hUM_apply]; exact LRf.Words.pullbackHom_iota0_heckeWordHom N q' (ws i) φ
  have hresU₁ : ∀ i, i < r → ∀ φ, RES1 N q' (UN i φ) = UM i (RES1 N q' φ) := by
    intro i _ φ; rw [hUN_apply, hUM_apply]; exact LRf.Words.pullbackHom_iota1_heckeWordHom N q' (ws i) φ

  have hβτ₀ : ∀ x, BETA0 N q' hq' hq'N (τM x) = τN (BETA0 N q' hq' hq'N x) := by
    intro x
    rw [hτM_aeval, hτN_aeval]
    exact LRf.Words.aeval_comm_of_comm (BETA0 N q' hq' hq'N)
      (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap
      (fun y => HeckeEis.degeneracyTransferZero_heckeOperatorHom_comm N q' hq' hq'N ℓ₀ hℓ₀p hℓ₀M y) m x
  have hβτ₁ : ∀ x, BETA1 N q' (τM x) = τN (BETA1 N q' x) := by
    intro x
    rw [hτM_aeval, hτN_aeval]
    exact LRf.Words.aeval_comm_of_comm (BETA1 N q')
      (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap
      (fun y => hbeta1 hq' hq'N ℓ₀ hℓ₀p hℓ₀M y) m x

  have hkill : ∀ φ ψ : Additive (Gamma0 N) →+ ℤ,
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
      (∃ χ : Additive (Gamma0 (N * q')) →+ ℤ, RES0 N q' φ + RES1 N q' ψ = (p : ℤ) • χ) →
        (∃ φ' : Additive (Gamma0 N) →+ ℤ, τN φ - m.eval ((ℓ₀ : ℤ) + 1) • φ = (p : ℤ) • φ') ∧
        (∃ ψ' : Additive (Gamma0 N) →+ ℤ, τN ψ - m.eval ((ℓ₀ : ℤ) + 1) • ψ = (p : ℤ) • ψ') := by
    intro φ ψ hφ hψ hχ
    obtain ⟨hφE, hψE⟩ := corloc_odd p hp hp2 hq' hq'N φ ψ hφ hψ hχ ℓ₀ hℓ₀p hℓ₀M
    rw [hτN_aeval, hτN_aeval]
    exact ⟨LRf.Words.exists_aeval_sub_eval_smul_eq (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap (p : ℤ)
        ((ℓ₀ : ℤ) + 1) φ hφE m,
      LRf.Words.exists_aeval_sub_eval_smul_eq (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap (p : ℤ)
        ((ℓ₀ : ℤ) + 1) ψ hψE m⟩

  obtain ⟨pair₁, pair₀, hperf₁, hperf₀, hadj₁, hadj₀, hproj₀, hproj₁⟩ := PDpairing_odd p hp hp2 N q' hq' hq'N
  have hTmemN : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
    fun x hx => (ModularCurve.Period.mem_parabolicHoms_iff).mpr
      (hTpar_int N ℓ₀ x ((ModularCurve.Period.mem_parabolicHoms_iff).mp hx))
  have hTmemM : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap x
        ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ :=
    fun x hx => (ModularCurve.Period.mem_parabolicHoms_iff).mpr
      (hTpar_int (N * q') ℓ₀ x ((ModularCurve.Period.mem_parabolicHoms_iff).mp hx))

  have hres_aevalN : ∀ x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      ((Polynomial.aeval ((HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap.restrict hTmemN) m x :
          ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) : Additive (Gamma0 N) →+ ℤ) = τN x := by
    intro x
    rw [hτN_aeval]
    exact LRf.Words.aeval_comm_of_comm_left
      (ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ).subtype.toAddMonoidHom
      ((HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap.restrict hTmemN)
      (HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap (fun _ => rfl) m x
  have hres_aevalM : ∀ x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      ((Polynomial.aeval ((HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap.restrict hTmemM) m x :
          ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ) : Additive (Gamma0 (N * q')) →+ ℤ) = τM x := by
    intro x
    rw [hτM_aeval]
    exact LRf.Words.aeval_comm_of_comm_left
      (ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ).subtype.toAddMonoidHom
      ((HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap.restrict hTmemM)
      (HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap (fun _ => rfl) m x
  have hadjτ₁ : ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ,
      pair₁ ⟨τM x, hτMpar x x.2⟩ y = pair₁ x ⟨τM y, hτMpar y y.2⟩ := by
    intro x y
    have hx : (⟨τM x, hτMpar x x.2⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        = Polynomial.aeval ((HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap.restrict hTmemM) m x :=
      Subtype.ext (hres_aevalM x).symm
    have hy : (⟨τM y, hτMpar y y.2⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q')) ℤ)
        = Polynomial.aeval ((HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap.restrict hTmemM) m y :=
      Subtype.ext (hres_aevalM y).symm
    rw [hx, hy]
    exact LRf.Words.aeval_selfAdjoint pair₁ ((HeckeEis.heckeOperatorHom (N * q') ℓ₀ ℤ).toIntLinearMap.restrict hTmemM)
      (fun a b => hadj₁ ℓ₀ hℓ₀p hℓ₀M a b) m x y
  have hadjτ₀ : ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      pair₀ ⟨τN x, hτNpar x x.2⟩ y = pair₀ x ⟨τN y, hτNpar y y.2⟩ := by
    intro x y
    have hx : (⟨τN x, hτNpar x x.2⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
        = Polynomial.aeval ((HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap.restrict hTmemN) m x :=
      Subtype.ext (hres_aevalN x).symm
    have hy : (⟨τN y, hτNpar y y.2⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
        = Polynomial.aeval ((HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap.restrict hTmemN) m y :=
      Subtype.ext (hres_aevalN y).symm
    rw [hx, hy]
    exact LRf.Words.aeval_selfAdjoint pair₀ ((HeckeEis.heckeOperatorHom N ℓ₀ ℤ).toIntLinearMap.restrict hTmemN)
      (fun a b => hadj₀ ℓ₀ hℓ₀p hℓ₀M a b) m x y

  obtain ⟨H, hHpar, hH₀, hH₁, hHne, hHU⟩ := LRf.Engine.assemble p τN τM hτNpar hτMpar UN UM (fun i => i < r)
    hUMpar hUcomm φ₀ hφ₀par hφ₀ne hφ₀τ hφ₀U c hc hφ₀q'
    (RES0 N q') (RES1 N q') hrespar0 hrespar1 hresτ₀ hresτ₁ hresU₀ hresU₁
    (BETA0 N q' hq' hq'N) (BETA1 N q') (hbetapar0 hq' hq'N) hbetapar1 hβτ₀ hβτ₁
    (hentry00 hq' hq'N) (hentry11 hq' hq'N) (hentry01 hq' hq'N) hentry10
    (m.eval ((ℓ₀ : ℤ) + 1)) hme hkill pair₁ pair₀ hperf₁ hperf₀ hadjτ₁ hadjτ₀ hproj₀ hproj₁

  exact LRf.Endgame.mem_comap_of_new_class hq' hq'N A p h𝔪 hp𝔪 χ₁ r ws hspan H hHpar hH₀ hH₁ hHne
    (fun i hi => by obtain ⟨ψ, hψ⟩ := hHU i hi; exact ⟨ψ, by rw [← hUM_apply]; exact hψ⟩)

#print axioms solution

end Assembly
p2m_reactivate "P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.LRf.Engine P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime.INHX2"

end S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime
end P2MW
export P2MW.S_LevelRaising_qNewSupport_comap_of_isNormalizedEigenform_oddPrime (solution)
