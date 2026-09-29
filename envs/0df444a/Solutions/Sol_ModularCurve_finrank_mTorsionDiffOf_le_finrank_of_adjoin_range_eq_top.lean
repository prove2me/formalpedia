-- Prove2me | solution 1 for ModularCurve.finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f480b37f-f99c-57e8-ae01-5b3ce29243fc

import Mathlib
import Definitions.Def_Module_CommFamilyAnnPart
import Definitions.Def_ModularCurve_MTorsionDiff
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
import Theorems.Thm_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero_of_natCast_ne_zero
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.cuspCount_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one"
p2m_attr_erase "simp" "ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve
open scoped TensorProduct

namespace E4Body

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc : (thetaL K (jqModC K)).coeff (-1) = 0 := by rw [h]; rfl
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, show (-1 : ℤ) - 1 = -2 by norm_num] at hc
  have hd := LaurentSeries.derivative_iterate_coeff (R := K) 1 (jqModC K) (-2)
  simp only [Function.iterate_one, Nat.cast_one] at hd
  rw [hd, show (-2 : ℤ) + 1 = -1 by norm_num, coeff_jqModC_neg_one] at hc

  simp [descPochhammer_one, Polynomial.smeval_X] at hc

theorem coeff_qExpansionDiffAlong_eq_zero_of_mem_regularDifferentials
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    {ω : Ω[↥(modularFunctionFieldC K N)⁄K]} (hω : ω ∈ regularDifferentials K (modularFunctionFieldC K N))
    (n : ℤ) (hn : n ≤ 0) :
    (qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff n = 0 := by
  obtain ⟨e, he⟩ :=
    ModularCurve.exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq K N hN

  let Φ : K ⊗[ℤ] ↥(CuspForm.intLattice N 2) →ₗ[K] LaurentSeries K :=
    qExpansionDiffAlong (modularFunctionFieldC K N).val ∘ₗ
      (regularDifferentials K (modularFunctionFieldC K N)).subtype ∘ₗ e.toLinearMap
  have hΦ : ∀ t, Φ t = qExpansionDiffAlong (modularFunctionFieldC K N).val
      (e t : Ω[↥(modularFunctionFieldC K N)⁄K]) := fun _ => rfl

  have hps : ∀ a : ℕ → ℤ, a 0 = 0 →
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m => (a m : K))).coeff n = 0 := by
    intro a ha0
    rcases lt_or_eq_of_le hn with hlt | rfl
    · rw [HahnSeries.ofPowerSeries_apply]
      exact HahnSeries.embDomain_notin_range (by
        rintro ⟨m, hm⟩
        first | omega | (simp at hm; done) | (simp at hm; omega))
    · rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff]
      simp [ha0]

  have hint : ∀ f : ↥(CuspForm.intLattice N 2), ∀ c : K, (Φ (c ⊗ₜ[ℤ] f)).coeff n = 0 := by
    rintro ⟨f, hf⟩
    induction hf using Submodule.span_induction with
    | mem g hg =>
      intro c
      obtain ⟨a, ha⟩ : ∃ a : ℕ → ℤ, ∀ m, ModularFormClass.qCoeff g m = (a m : ℂ) :=
        ⟨fun m => (hg m).choose, fun m => (hg m).choose_spec⟩
      have ha0 : a 0 = 0 := by
        have : (a 0 : ℂ) = 0 := by rw [← ha 0]; exact CuspForm.qCoeff_zero g
        exact_mod_cast this
      rw [hΦ, he c ⟨g, Submodule.subset_span hg⟩ a ha, HahnSeries.coeff_smul, smul_eq_mul, hps a ha0,
        mul_zero]
    | zero =>
      intro c
      have h0 : (⟨0, Submodule.zero_mem _⟩ : ↥(CuspForm.intLattice N 2)) = 0 := rfl
      rw [h0, TensorProduct.tmul_zero, Φ.map_zero, HahnSeries.coeff_zero]
    | add g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      intro c
      have : (c ⊗ₜ[ℤ] (⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂⟩ : ↥(CuspForm.intLattice N 2))) =
          c ⊗ₜ[ℤ] ⟨g₁, hg₁⟩ + c ⊗ₜ[ℤ] ⟨g₂, hg₂⟩ := by
        rw [← TensorProduct.tmul_add]; rfl
      rw [this, Φ.map_add, HahnSeries.coeff_add, ih₁, ih₂, add_zero]
    | smul r g hg ih =>
      intro c
      have : (c ⊗ₜ[ℤ] (⟨r • g, Submodule.smul_mem _ r hg⟩ : ↥(CuspForm.intLattice N 2))) =
          (r • c) ⊗ₜ[ℤ] ⟨g, hg⟩ := by
        rw [TensorProduct.smul_tmul]; rfl
      rw [this]; exact ih (r • c)

  obtain ⟨t, ht⟩ : ∃ t, e t = ⟨ω, hω⟩ := e.surjective ⟨ω, hω⟩
  have hω' : qExpansionDiffAlong (modularFunctionFieldC K N).val ω = Φ t := by
    rw [hΦ, ht]
  rw [hω']
  clear hω' ht
  induction t using TensorProduct.induction_on with
  | zero => rw [Φ.map_zero, HahnSeries.coeff_zero]
  | tmul c f => exact hint f c
  | add x y hx hy => rw [Φ.map_add, HahnSeries.coeff_add, hx, hy, add_zero]

def Qp (K : Type*) [Field K] : Submodule K (LaurentSeries K) :=
  ⨅ n : {n : ℤ // n ≤ 0}, LinearMap.ker (HahnSeries.coeff.linearMap (n : ℤ) : LaurentSeries K →ₗ[K] K)

theorem mem_Qp_iff (K : Type*) [Field K] (f : LaurentSeries K) :
    f ∈ Qp K ↔ ∀ n : ℤ, n ≤ 0 → f.coeff n = 0 := by
  simp only [Qp, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  rfl

theorem heckeU_mem_Qp (K : Type*) [Field K] (ℓ : ℕ) (hℓ : 0 < ℓ) (f : LaurentSeries K) (hf : f ∈ Qp K) :
    LaurentSeries.heckeU K ℓ hℓ f ∈ Qp K := by
  rw [mem_Qp_iff] at hf ⊢
  intro n hn
  rw [LaurentSeries.coeff_heckeU]
  apply hf
  have : (0 : ℤ) ≤ ℓ := by exact_mod_cast hℓ.le
  nlinarith

theorem heckeT_mem_Qp (K : Type*) [Field K] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) (f : LaurentSeries K)
    (hf : f ∈ Qp K) : LaurentSeries.heckeT K ℓ hℓ k f ∈ Qp K := by
  rw [mem_Qp_iff] at hf ⊢
  intro n hn
  rw [LaurentSeries.coeff_heckeT]
  have h1 : f.coeff (ℓ * n) = 0 := by
    apply hf
    have : (0 : ℤ) ≤ ℓ := by exact_mod_cast hℓ.le
    nlinarith
  have h2 : (if ((ℓ : ℕ) : ℤ) ∣ n then f.coeff (n / (ℓ : ℕ)) else 0) = 0 := by
    split_ifs with hd
    · apply hf
      obtain ⟨c, rfl⟩ := hd
      have hℓ0 : ((ℓ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
      rw [Int.mul_ediv_cancel_left _ hℓ0]
      have : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
      nlinarith
    · rfl
  rw [h1, h2, mul_zero, add_zero]

end E4Body

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (Fam : Module.End.CommFamily K (LaurentSeries K) Nat.Primes)
    (hFamT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N → Fam.T ℓ = LaurentSeries.heckeT K (ℓ : ℕ) ℓ.2.pos 2)
    (hFamU : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N → Fam.T ℓ = LaurentSeries.heckeU K (ℓ : ℕ) ℓ.2.pos)
    {k₀ : Type*} [Field k₀] [Finite k₀] [Algebra (ZMod p) k₀]
    (θ₀ : Nat.Primes → k₀) (hgen : Algebra.adjoin (ZMod p) (Set.range θ₀) = ⊤) (e : k₀ →+* K) :
    FiniteDimensional K ↥(mTorsionDiffOf K p N Fam (e ∘ θ₀)) ∧
      Module.finrank K ↥(mTorsionDiffOf K p N Fam (e ∘ θ₀)) ≤ Module.finrank (ZMod p) k₀ := by
  classical
  set φ := qExpansionDiffAlong (modularFunctionFieldC K N).val with hφ

  have hW : ∀ (a : Nat.Primes) (v : LaurentSeries K), v ∈ E4Body.Qp K → Fam.T a v ∈ E4Body.Qp K := by
    intro a v hv
    by_cases ha : (a : ℕ) ∣ N
    · rw [hFamU a ha]; exact E4Body.heckeU_mem_Qp K _ _ v hv
    · rw [hFamT a ha]; exact E4Body.heckeT_mem_Qp K _ _ 2 v hv
  have hd : ∀ τ : k₀ →+* K,
      FiniteDimensional K ↥(E4Body.Qp K ⊓ ⨅ a : Nat.Primes, LinearMap.ker (Fam.T a - τ (θ₀ a) • LinearMap.id)) ∧
        Module.finrank K ↥(E4Body.Qp K ⊓ ⨅ a : Nat.Primes, LinearMap.ker (Fam.T a - τ (θ₀ a) • LinearMap.id)) ≤ 1 := by
    intro τ
    set E := E4Body.Qp K ⊓ ⨅ a : Nat.Primes, LinearMap.ker (Fam.T a - τ (θ₀ a) • LinearMap.id) with hE
    let L : ↥E →ₗ[K] K := (HahnSeries.coeff.linearMap (1 : ℤ) : LaurentSeries K →ₗ[K] K) ∘ₗ E.subtype
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨f, hf⟩ hL
      rw [LinearMap.mem_ker] at hL
      obtain ⟨hQ, hEig⟩ := Submodule.mem_inf.mp hf
      rw [E4Body.mem_Qp_iff] at hQ
      rw [Submodule.mem_iInf] at hEig
      have heig : ∀ a : Nat.Primes, Fam.T a f = τ (θ₀ a) • f := by
        intro a
        have := hEig a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero] at this
        exact this
      have hzero : f = 0 := by
        refine LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero K N 2
          (fun ℓ => τ (θ₀ ℓ)) f hQ ?_ ?_ hL
        · intro ℓ hℓ
          have := heig ℓ
          rwa [hFamT ℓ hℓ] at this
        · intro q hq
          have := heig q
          rwa [hFamU q hq] at this
      exact Subtype.ext hzero
    haveI : FiniteDimensional K ↥E := Module.Finite.of_injective L hinj
    exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_injective hinj).trans (Module.finrank_self K).le⟩
  obtain ⟨hfinQ, hrankQ⟩ :=
    Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
      Fam p θ₀ hgen e (E4Body.Qp K) hW 1 hd

  set S := mTorsionDiffOf K p N Fam (e ∘ θ₀) with hS
  set T := E4Body.Qp K ⊓ Fam.annPart p (e ∘ θ₀) with hT
  have hmap : ∀ ω ∈ S, φ ω ∈ T := by
    intro ω hω
    obtain ⟨hreg, hann⟩ := Submodule.mem_inf.mp hω
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_comap.mp hann⟩
    rw [E4Body.mem_Qp_iff]
    intro n hn
    exact E4Body.coeff_qExpansionDiffAlong_eq_zero_of_mem_regularDifferentials K N hN hreg n hn
  let ψ : ↥S →ₗ[K] ↥T := (φ ∘ₗ S.subtype).codRestrict T (fun ω => hmap ω ω.2)
  have hψ : Function.Injective ψ := by
    have hinjφ :=
      ModularCurve.qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero_of_natCast_ne_zero
        K N hN (modularFunctionFieldC K N).val (E4Body.thetaL_jqModC_ne_zero K)
    intro x y hxy
    apply Subtype.ext
    apply hinjφ
    have := congrArg (fun z : ↥T => (z : LaurentSeries K)) hxy
    simpa [ψ] using this
  haveI : FiniteDimensional K ↥T := hfinQ
  haveI : FiniteDimensional K ↥S := Module.Finite.of_injective ψ hψ
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank K ↥S ≤ Module.finrank K ↥T := LinearMap.finrank_le_finrank_of_injective hψ
    _ ≤ Module.finrank (ZMod p) k₀ * 1 := hrankQ
    _ = Module.finrank (ZMod p) k₀ := Nat.mul_one _

end S_ModularCurve_finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top
end P2MW
export P2MW.S_ModularCurve_finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top (solution)
