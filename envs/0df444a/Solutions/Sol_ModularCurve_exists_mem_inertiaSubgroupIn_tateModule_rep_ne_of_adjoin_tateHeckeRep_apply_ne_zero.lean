-- Prove2me | solution 1 for ModularCurve.exists_mem_inertiaSubgroupIn_tateModule_rep_ne_of_adjoin_tateHeckeRep_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/090603ca-8ecf-500a-b04e-c731603e6672

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_Submodule_mem_of_forall_exists_sub_mem_pow_smul_top
import Theorems.Thm_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_CuspForm_heckeEvalForms_range_eq_top
import Theorems.Thm_ModularCurve_ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar
import Theorems.Thm_ModularCurve_exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar
import Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
import Theorems.Thm_ModularCurve_tateModule_rep_comp_tateHeckeRep_comm
import Theorems.Thm_ModularCurve_isReduced_rationalHeckeAlgebra
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_inertiaSubgroupIn_tateModule_rep_ne_of_adjoin_tateHeckeRep_apply_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.attachmentTraceData_apply_prime TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL"
p2m_attr_erase "simp" "HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"
p2m_attr_erase "simp" "AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 8000000

p2m_open "ModularCurve~TateModule P2MW.S_ModularCurve_exists_mem_inertiaSubgroupIn_tateModule_rep_ne_of_adjoin_tateHeckeRep_apply_ne_zero.ModularCurve CuspForm"
open scoped Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

variable (p : ℕ) [Fact p.Prime]

section levelwise
variable [Module HeckeAlg (JZero p)]

def IsEis (x : _root_.TateModule 2 (JZero p)) : Prop :=
  ∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M

end levelwise

theorem smul_eq_zero_of_mem_ker (t : HeckeAlg)
    (ht : t ∈ RingHom.ker ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))) (y : JZero p) :
    (letI := heckeModuleBar p; t • y) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := heckeOperatorsCommuteBar p
  rw [ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar p h, RingHom.mem_ker] at ht
  rw [heckeModuleBar_smul_def h, ht]
  rfl

theorem smul_eq_zero_of_mem_span_pow (n : ℕ) (t : HeckeAlg)
    (ht : ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t ∈
      Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ n})
    (y : JZero p) (hy : 2 ^ n • y = 0) :
    (letI := heckeModuleBar p; t • y) = 0 := by
  letI := heckeModuleBar p
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set e := (latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2) with he
  have hsurj : Function.Surjective e := by
    rw [he, RingHom.coe_comp]
    exact (latticeRestrictHom_surjective p ∅).comp
      (RingHom.range_eq_top.mp (heckeEvalForms_range_eq_top p 2))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp ht
  obtain ⟨v, rfl⟩ := hsurj w

  have hk : t - ((2 : ℕ) : HeckeAlg) ^ n * v ∈ RingHom.ker e := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, ← hw, mul_comm, sub_self]
  have h1 : (t - ((2 : ℕ) : HeckeAlg) ^ n * v) • y = 0 := smul_eq_zero_of_mem_ker p _ hk y
  rw [sub_smul, sub_eq_zero] at h1
  rw [h1, mul_smul]
  have : (((2 : ℕ) : HeckeAlg) ^ n) • (v • y) = (2 ^ n : ℕ) • (v • y) := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [this, smul_comm, hy, smul_zero]

end ModularCurve.NonTriv

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

variable (p : ℕ) [Fact p.Prime]

section tower

structure Tower (te : ℕ → HeckeAlg) : Prop where
  cauchy : ∀ m : ℕ,
    ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te (m + 1)) -
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
      Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}
  fix : letI := heckeModuleBar p
    ∀ m M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M, 2 ^ m • x = 0 → te m • x = x
  into : letI := heckeModuleBar p
    ∀ m : ℕ, ∀ y : JZero p, 2 ^ m • y = 0 → ∃ M : ℕ, te m • y ∈ eisensteinTorsionBar p 2 M

variable {p}
variable {te : ℕ → HeckeAlg}

theorem Tower.cauchy_le (h : Tower p te) {a b : ℕ} (hab : b ≤ a) :
    ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te a) -
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te b) ∈
      Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ b} := by
  induction a, hab using Nat.le_induction with
  | base => simp
  | succ a hab ih =>
      have hstep := h.cauchy a
      have hle : Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ a} ≤
          Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ b} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hab)
      have := Ideal.add_mem _ (hle hstep) ih
      rwa [sub_add_sub_cancel] at this

theorem Tower.sub_smul_eq_zero (h : Tower p te) {a b : ℕ} (hab : b ≤ a) (y : JZero p) (hy : 2 ^ b • y = 0) :
    (letI := heckeModuleBar p; (te a - te b) • y) = 0 :=
  smul_eq_zero_of_mem_span_pow p b (te a - te b) (by rw [map_sub]; exact h.cauchy_le hab) y hy

theorem pow_smul_apply_eq_zero (x : _root_.TateModule 2 (JZero p)) (n : ℕ) :
    2 ^ n • (x : ℕ → JZero p) n = 0 := by
  have := _root_.TateModule.torsion x n
  rwa [natCast_zsmul] at this

theorem eisProjFun_mem (h : Tower p te) (x : _root_.TateModule 2 (JZero p)) :
    (letI := heckeModuleBar p; fun n => te n • (x : ℕ → JZero p) n) ∈ _root_.TateModule 2 (JZero p) := by
  letI := heckeModuleBar p
  intro n
  refine ⟨?_, ?_⟩
  · show ((2 ^ n : ℕ) : ℤ) • (te n • (x : ℕ → JZero p) n) = 0
    rw [natCast_zsmul, smul_comm, pow_smul_apply_eq_zero x n, smul_zero]
  · show ((2 : ℕ) : ℤ) • (te (n + 1) • (x : ℕ → JZero p) (n + 1)) = te n • (x : ℕ → JZero p) n
    rw [smul_comm, _root_.TateModule.compat x n]
    have h0 := h.sub_smul_eq_zero (Nat.le_succ n) ((x : ℕ → JZero p) n) (pow_smul_apply_eq_zero x n)
    rw [sub_smul, sub_eq_zero] at h0
    exact h0

noncomputable def eisProj (h : Tower p te) : letI := heckeModuleBar p
    _root_.TateModule 2 (JZero p) →ₗ[ℤ_[2]] _root_.TateModule 2 (JZero p) :=
  letI := heckeModuleBar p
  { toFun := fun x => ⟨_, eisProjFun_mem h x⟩
    map_add' := fun x y => Subtype.ext (funext fun n => by
      show te n • ((x + y : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n = _
      rw [_root_.TateModule.coe_add, Pi.add_apply, smul_add]
      rfl)
    map_smul' := fun a x => Subtype.ext (funext fun n => by
      show te n • ((a • x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n =
        ((a • (⟨_, eisProjFun_mem h x⟩ : _root_.TateModule 2 (JZero p)) : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n
      rw [_root_.TateModule.smul_apply, _root_.TateModule.smul_apply, smul_comm]) }

theorem eisProj_apply (h : Tower p te) (x : _root_.TateModule 2 (JZero p)) (n : ℕ) :
    ((eisProj h x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n =
      (letI := heckeModuleBar p; te n • (x : ℕ → JZero p) n) :=
  rfl

theorem isEis_eisProj (h : Tower p te) (x : _root_.TateModule 2 (JZero p)) :
    letI := heckeModuleBar p; IsEis p (eisProj h x) := by
  letI := heckeModuleBar p
  intro n
  obtain ⟨M, hM⟩ := h.into n ((x : ℕ → JZero p) n) (pow_smul_apply_eq_zero x n)
  exact ⟨M, hM⟩

theorem eisProj_eq_self (h : Tower p te) (x : _root_.TateModule 2 (JZero p))
    (hx : letI := heckeModuleBar p; IsEis p x) : eisProj h x = x := by
  letI := heckeModuleBar p
  refine Subtype.ext (funext fun n => ?_)
  rw [eisProj_apply]
  obtain ⟨M, hM⟩ := hx n
  exact h.fix n M _ hM (pow_smul_apply_eq_zero x n)

theorem eisProj_idem (h : Tower p te) (x : _root_.TateModule 2 (JZero p)) :
    eisProj h (eisProj h x) = eisProj h x :=
  eisProj_eq_self h _ (isEis_eisProj h x)

theorem eisProj_comm_tateHeckeRep (h : Tower p te) (t : HeckeAlg) (x : _root_.TateModule 2 (JZero p)) :
    letI := heckeModuleBar p
    eisProj h (tateHeckeRep 2 (JZero p) t x) = tateHeckeRep 2 (JZero p) t (eisProj h x) := by
  letI := heckeModuleBar p
  refine Subtype.ext (funext fun n => ?_)
  rw [eisProj_apply, coe_tateHeckeRep_apply_apply, coe_tateHeckeRep_apply_apply, eisProj_apply,
    ← mul_smul, ← mul_smul, mul_comm]

theorem eisProj_comm_rep (h : Tower p te)
    [letI := heckeModuleBar p; SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero p)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : _root_.TateModule 2 (JZero p)) :
    eisProj h (_root_.TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) =
      _root_.TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (eisProj h x) := by
  letI := heckeModuleBar p
  haveI : SMulCommClass HeckeAlg (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p) := SMulCommClass.symm _ _ _
  refine Subtype.ext (funext fun n => ?_)
  rw [eisProj_apply, _root_.TateModule.rep_apply, _root_.TateModule.rep_apply, eisProj_apply, smul_comm]

theorem exists_linearMap_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (c : R) (hc : c ≠ 0) (D : M →ₗ[R] M)
    (h : ∀ x : M, ∃ y : M, D x = c • y) : ∃ F : M →ₗ[R] M, D = c • F := by
  choose f hf using h
  have inj : ∀ a b : M, c • a = c • b → a = b := fun a b hab => by
    have h1 : c • (a - b) = 0 := by rw [smul_sub, hab, sub_self]
    exact sub_eq_zero.mp ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h1).resolve_left hc)
  have hadd : ∀ x y, f (x + y) = f x + f y := fun x y => by
    apply inj
    rw [smul_add, ← hf, ← hf, ← hf, map_add]
  have hsmul : ∀ (a : R) x, f (a • x) = a • f x := fun a x => by
    apply inj
    rw [← hf, smul_comm c a, ← hf, map_smul]
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, LinearMap.ext fun x => ?_⟩
  rw [LinearMap.smul_apply]
  exact hf x

theorem exists_eisProj_sub_eq_pow_smul (h : Tower p te) (n : ℕ)
    [NoZeroSMulDivisors ℤ_[2] (_root_.TateModule 2 (JZero p))] :
    letI := heckeModuleBar p
    ∃ F : _root_.TateModule 2 (JZero p) →ₗ[ℤ_[2]] _root_.TateModule 2 (JZero p),
      eisProj h - tateHeckeRep 2 (JZero p) (te n) = ((2 : ℕ) : ℤ_[2]) ^ n • F := by
  letI := heckeModuleBar p

  have hmem : ∀ x : _root_.TateModule 2 (JZero p),
      (fun k => (te (k + n) - te n) • (x : ℕ → JZero p) (k + n)) ∈ _root_.TateModule 2 (JZero p) := by
    intro x k
    refine ⟨?_, ?_⟩
    · show ((2 ^ k : ℕ) : ℤ) • ((te (k + n) - te n) • (x : ℕ → JZero p) (k + n)) = 0
      rw [smul_comm, show k + n = n + k from Nat.add_comm k n, _root_.TateModule.compat_pow x n k]
      exact h.sub_smul_eq_zero (Nat.le_add_right n k) _ (pow_smul_apply_eq_zero x n)
    · show ((2 : ℕ) : ℤ) • ((te (k + 1 + n) - te n) • (x : ℕ → JZero p) (k + 1 + n)) =
        (te (k + n) - te n) • (x : ℕ → JZero p) (k + n)
      rw [smul_comm, show k + 1 + n = (k + n) + 1 by omega, _root_.TateModule.compat x (k + n)]
      have h0 := h.sub_smul_eq_zero (Nat.le_succ (k + n)) ((x : ℕ → JZero p) (k + n))
        (pow_smul_apply_eq_zero x (k + n))
      rw [sub_smul, sub_eq_zero] at h0
      rw [sub_smul, sub_smul, h0]
  refine exists_linearMap_eq_smul _ (pow_ne_zero n (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0))) _
    fun x => ⟨⟨_, hmem x⟩, Subtype.ext (funext fun k => ?_)⟩
  rw [LinearMap.sub_apply, AddSubgroupClass.coe_sub, Pi.sub_apply, eisProj_apply, coe_tateHeckeRep_apply_apply,
    ← Nat.cast_pow, _root_.TateModule.natCast_padicInt_smul_apply]
  show te k • (x : ℕ → JZero p) k - te n • (x : ℕ → JZero p) k =
    ((2 ^ n : ℕ) : ℤ) • ((te (k + n) - te n) • (x : ℕ → JZero p) (k + n))
  rw [smul_comm, _root_.TateModule.compat_pow x k n, sub_smul]
  have h0 := h.sub_smul_eq_zero (Nat.le_add_right k n) ((x : ℕ → JZero p) k) (pow_smul_apply_eq_zero x k)
  rw [sub_smul, sub_eq_zero] at h0
  rw [h0]

end tower

end ModularCurve.NonTriv

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

variable (p : ℕ) [Fact p.Prime]

theorem noZeroSMulDivisors_tateModule : NoZeroSMulDivisors ℤ_[2] (_root_.TateModule 2 (JZero p)) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hval := PadicInt.unitCoeff_spec ha
  have hk : ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val * a = ((2 : ℕ) : ℤ_[2]) ^ a.valuation :=
    (congrArg (fun z => ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val * z) hval).trans
      (by rw [← mul_assoc, Units.inv_mul, one_mul])
  have hz : ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val • (0 : _root_.TateModule 2 (JZero p)) = 0 :=
    Subtype.ext (funext fun n => by
      rw [_root_.TateModule.smul_apply, _root_.TateModule.coe_zero, Pi.zero_apply, zsmul_zero])
  have h2 : ((2 : ℕ) : ℤ_[2]) ^ a.valuation • x = 0 := by
    rw [← hk, mul_smul, h]
    exact hz
  refine Subtype.ext (funext fun n => ?_)
  have hc := _root_.TateModule.compat_pow x n a.valuation
  have hn := congrArg (fun y : _root_.TateModule 2 (JZero p) => (y : ℕ → JZero p) (n + a.valuation)) h2
  simp only [_root_.TateModule.coe_zero, Pi.zero_apply] at hn
  rw [← Nat.cast_pow, _root_.TateModule.natCast_padicInt_smul_apply] at hn
  rw [_root_.TateModule.coe_zero, Pi.zero_apply, ← hc]
  exact hn

section withModule
variable [Module HeckeAlg (JZero p)]

theorem rationalHeckeRep_comm :
    ∀ a ∈ Set.range (rationalHeckeRep 2 (JZero p)), ∀ b ∈ Set.range (rationalHeckeRep 2 (JZero p)),
      a * b = b * a := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

@[reducible] noncomputable def instCommRingA : CommRing ↥(rationalHeckeAlgebra 2 (JZero p)) :=
  { (inferInstance : Ring ↥(rationalHeckeAlgebra 2 (JZero p))) with
    mul_comm := fun a b => by
      have h := @mul_comm _ (Algebra.adjoinCommRingOfComm ℚ_[2] (rationalHeckeRep_comm p)).toCommMagma a b
      exact h }

theorem moduleFinite_V : Module.Finite ℚ_[2] (RationalTateModule 2 (JZero p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.moduleFinite_padicInt_tateModule_jZero p 2
  infer_instance

theorem finiteDimensional_A : FiniteDimensional ℚ_[2] ↥(rationalHeckeAlgebra 2 (JZero p)) := by
  haveI := moduleFinite_V p
  exact Module.Finite.of_injective (rationalHeckeAlgebra 2 (JZero p)).val.toLinearMap Subtype.val_injective

theorem isArtinianRing_A : letI := instCommRingA p; IsArtinianRing ↥(rationalHeckeAlgebra 2 (JZero p)) := by
  letI := instCommRingA p
  haveI := finiteDimensional_A p
  exact IsArtinianRing.of_finite ℚ_[2] _

theorem baseChange_mem_rationalHeckeAlgebra {α : Module.End ℤ_[2] (_root_.TateModule 2 (JZero p))}
    (hα : α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t)) :
    α.baseChange ℚ_[2] ∈ rationalHeckeAlgebra 2 (JZero p) := by
  have hmap : Subalgebra.map (Module.End.baseChangeHom ℤ_[2] ℚ_[2] (_root_.TateModule 2 (JZero p)))
      (Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t)) ≤
      (rationalHeckeAlgebra 2 (JZero p)).restrictScalars ℤ_[2] := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact rationalHeckeRep_mem_rationalHeckeAlgebra 2 (JZero p) t
  exact hmap ⟨α, hα, rfl⟩

theorem baseChange_one_tmul (α : Module.End ℤ_[2] (_root_.TateModule 2 (JZero p))) (x : _root_.TateModule 2 (JZero p)) :
    α.baseChange ℚ_[2] ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] x) = (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] α x :=
  LinearMap.baseChange_tmul _ _ _

end withModule

theorem eisProj_mem_adjoin {te : ℕ → HeckeAlg} (h : Tower p te) :
    letI := heckeModuleBar p
    eisProj h ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t) := by
  letI := heckeModuleBar p
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.moduleFinite_padicInt_tateModule_jZero p 2
  haveI := noZeroSMulDivisors_tateModule p
  haveI : Module.Free ℤ_[2] (_root_.TateModule 2 (JZero p)) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ_[2] (Module.End ℤ_[2] (_root_.TateModule 2 (JZero p))) := inferInstance
  refine Submodule.mem_of_forall_exists_sub_mem_pow_smul_top (p := 2)
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t)))
    (eisProj h) fun n => ?_
  obtain ⟨F, hF⟩ := exists_eisProj_sub_eq_pow_smul h n
  refine ⟨tateHeckeRep 2 (JZero p) (te n), Algebra.subset_adjoin ⟨te n, rfl⟩, ?_⟩
  rw [hF]
  exact Submodule.smul_mem_pointwise_smul F _ ⊤ Submodule.mem_top

end ModularCurve.NonTriv

namespace IsArtinianRing
p2m_export "IsArtinianRing" "of_finite equivPi"
p2m_open "IsArtinianRing"

variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem equivPi_apply_eq_mk (a : A) (I : MaximalSpectrum A) :
    equivPi A a I = Ideal.Quotient.mk I.asIdeal a := by
  change equivPi A (algebraMap A A a) I = _
  rw [AlgEquiv.commutes]
  rfl

theorem exists_isIdempotentElem_and_span_singleton_eq (a : A) :
    ∃ e : A, IsIdempotentElem e ∧ Ideal.span {a} = Ideal.span {e} := by
  classical

  have hreg : ∀ I : MaximalSpectrum A, ∃ y : A ⧸ I.asIdeal, equivPi A a I * y * equivPi A a I = equivPi A a I := by
    intro I
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    by_cases h0 : equivPi A a I = 0
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨(equivPi A a I)⁻¹, by rw [mul_inv_cancel₀ h0, one_mul]⟩
  choose y hy using hreg
  let x : A := (equivPi A).symm y
  have hx : a * x * a = a := by
    apply (equivPi A).injective
    funext I
    rw [map_mul, map_mul]
    change equivPi A a I * (equivPi A ((equivPi A).symm y)) I * equivPi A a I = equivPi A a I
    rw [AlgEquiv.apply_symm_apply]
    exact hy I
  refine ⟨a * x, ?_, ?_⟩
  ·
    change a * x * (a * x) = a * x
    rw [← mul_assoc, hx]
  · apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨a, by rw [← mul_assoc, mul_right_comm, hx]⟩
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨x, by rw [mul_comm]⟩

theorem exists_isIdempotentElem_notMem_and_forall_mem (𝔪 : MaximalSpectrum A) :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ 𝔪.asIdeal ∧ ∀ 𝔪' : MaximalSpectrum A, 𝔪' ≠ 𝔪 → e ∈ 𝔪'.asIdeal := by
  classical
  let e : A := (equivPi A).symm (Pi.single 𝔪 1)
  have he : ∀ I, equivPi A e I = (Pi.single 𝔪 1 : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) I := fun I => by
    change (equivPi A ((equivPi A).symm (Pi.single 𝔪 1))) I = _
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨e, ?_, ?_, ?_⟩
  · apply (equivPi A).injective
    funext I
    rw [map_mul]
    change equivPi A e I * equivPi A e I = equivPi A e I
    rw [he]
    by_cases hI : I = 𝔪
    · subst hI; rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hI, mul_zero]
  · intro hmem
    have h1 : equivPi A e 𝔪 = 0 := by rw [equivPi_apply_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [he, Pi.single_eq_same] at h1
    exact one_ne_zero h1
  · intro 𝔪' hne
    have h1 : equivPi A e 𝔪' = 0 := by rw [he, Pi.single_eq_of_ne hne]
    rw [equivPi_apply_eq_mk] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem eq_zero_of_forall_mem (a : A) (h : ∀ 𝔪 : MaximalSpectrum A, a ∈ 𝔪.asIdeal) : a = 0 := by
  apply (equivPi A).injective
  rw [map_zero]
  funext I
  rw [equivPi_apply_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (h I)

end IsArtinianRing

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

theorem one_tmul_injective :
    Function.Injective (fun x : _root_.TateModule 2 (JZero p) => ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] x : RationalTateModule 2 (JZero p))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := noZeroSMulDivisors_tateModule p
  haveI : Module.Finite ℤ_[2] (_root_.TateModule 2 (JZero p)) := ModularCurve.moduleFinite_padicInt_tateModule_jZero p 2
  haveI : Module.Free ℤ_[2] (_root_.TateModule 2 (JZero p)) := Module.free_of_finite_type_torsion_free'
  intro x y hxy
  have h : (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (x - y) = (0 : RationalTateModule 2 (JZero p)) := by
    rw [TensorProduct.tmul_sub]; exact sub_eq_zero.mpr hxy
  suffices hs : x - y = 0 from sub_eq_zero.mp hs
  set z := x - y
  let b := Module.Free.chooseBasis ℤ_[2] (_root_.TateModule 2 (JZero p))
  let b' := Algebra.TensorProduct.basis ℚ_[2] b
  have hz : b'.repr ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] z) = 0 := by rw [h, map_zero]
  refine b.ext_elem fun i => ?_
  have hi := congrArg (fun f => f i) hz
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul] at hi
  rw [map_zero, Finsupp.zero_apply]
  rw [Finsupp.mapRange_apply] at hi
  exact (IsFractionRing.injective ℤ_[2] ℚ_[2]) (hi.trans (map_zero _).symm)

section withModule
variable [Module HeckeAlg (JZero p)]

theorem rationalGaloisRep_smul_comm
    (hgen : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlg),
      rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ∘ₗ rationalHeckeRep 2 (JZero p) t =
        rationalHeckeRep 2 (JZero p) t ∘ₗ rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ↥(rationalHeckeAlgebra 2 (JZero p)))
    (v : RationalTateModule 2 (JZero p)) :
    rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (a • v) =
      a • rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v := by
  obtain ⟨f, hf⟩ := a
  show rationalGaloisRep 2 (JZero p) _ σ (f v) = f (rationalGaloisRep 2 (JZero p) _ σ v)
  induction hf using Algebra.adjoin_induction generalizing v with
  | mem g hg =>
      obtain ⟨t, rfl⟩ := hg
      exact LinearMap.congr_fun (hgen σ t) v
  | algebraMap r =>
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add g g' _ _ hg hg' =>
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hg, hg']
  | mul g g' _ _ hg hg' =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hg, hg']

end withModule

theorem eisensteinTorsionBar_mono {M M' : ℕ} (h : M ≤ M') :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    eisensteinTorsionBar p 2 M ≤ eisensteinTorsionBar p 2 M' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := heckeModuleBar p
  intro x hx
  exact Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_pow_right h) hx

theorem isEis_of_mem_adjoin {α : Module.End ℤ_[2] (_root_.TateModule 2 (JZero p))}
    (hα : letI := heckeModuleBar p
      α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t))
    {x : _root_.TateModule 2 (JZero p)} (hx : IsEis p x) : IsEis p (α x) := by
  letI := heckeModuleBar p
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  induction hα using Algebra.adjoin_induction generalizing x with
  | mem g hg =>
      obtain ⟨t, rfl⟩ := hg
      intro n
      obtain ⟨M, hM⟩ := hx n
      exact ⟨M, by rw [coe_tateHeckeRep_apply_apply]; exact Submodule.smul_mem _ t hM⟩
  | algebraMap r =>
      intro n
      obtain ⟨M, hM⟩ := hx n
      refine ⟨M, ?_⟩
      rw [Module.algebraMap_end_apply, _root_.TateModule.smul_apply]
      exact AddSubgroup.zsmul_mem _ hM _
  | add g g' _ _ hg hg' =>
      intro n
      obtain ⟨M, hM⟩ := hg hx n
      obtain ⟨M', hM'⟩ := hg' hx n
      refine ⟨max M M', ?_⟩
      rw [LinearMap.add_apply, _root_.TateModule.coe_add, Pi.add_apply]
      exact AddSubgroup.add_mem _ (eisensteinTorsionBar_mono p (le_max_left M M') hM)
        (eisensteinTorsionBar_mono p (le_max_right M M') hM')
  | mul g g' _ _ hg hg' =>
      intro n
      exact hg (hg' hx) n

end ModularCurve.NonTriv

namespace IsArtinianRing
p2m_export "IsArtinianRing" "of_finite equivPi"
p2m_open "IsArtinianRing"

variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem exists_primitive_idempotent_package
    (a ε : A) (hε : IsIdempotentElem ε) (h : a * ε ≠ 0) :
    ∃ (𝔪 : MaximalSpectrum A) (e a' : A),
      IsIdempotentElem e ∧ e ∉ 𝔪.asIdeal ∧
      (∀ z : A, z * e = 0 ↔ z ∈ 𝔪.asIdeal) ∧
      1 - e ∈ 𝔪.asIdeal ∧
      a * ε * (a' * e) = e ∧
      ε * e = e := by
  classical

  have hex : ∃ 𝔪 : MaximalSpectrum A, a * ε ∉ 𝔪.asIdeal := by
    by_contra hall
    exact h (eq_zero_of_forall_mem (a * ε) fun 𝔪 => by_contra fun h𝔪 => hall ⟨𝔪, h𝔪⟩)
  obtain ⟨𝔪, h𝔪⟩ := hex
  have hprime := 𝔪.isMaximal.isPrime
  have ha : a ∉ 𝔪.asIdeal := fun ha => h𝔪 (𝔪.asIdeal.mul_mem_right ε ha)
  have hεm : ε ∉ 𝔪.asIdeal := fun hεm => h𝔪 (𝔪.asIdeal.mul_mem_left a hεm)

  obtain ⟨e, he, hem, heo⟩ := exists_isIdempotentElem_notMem_and_forall_mem 𝔪

  have hann : ∀ z : A, z * e = 0 ↔ z ∈ 𝔪.asIdeal := by
    intro z
    constructor
    · intro hz
      have : z * e ∈ 𝔪.asIdeal := by rw [hz]; exact 𝔪.asIdeal.zero_mem
      exact (hprime.mem_or_mem this).resolve_right hem
    · intro hz
      apply eq_zero_of_forall_mem
      intro 𝔪'
      by_cases h' : 𝔪' = 𝔪
      · subst h'; exact 𝔪'.asIdeal.mul_mem_right e hz
      · exact 𝔪'.asIdeal.mul_mem_left z (heo 𝔪' h')

  have h1e : 1 - e ∈ 𝔪.asIdeal := by
    rw [← hann]
    rw [sub_mul, one_mul, he.eq, sub_self]

  have hε1 : ε - 1 ∈ 𝔪.asIdeal := by
    have h0 : ε * (ε - 1) = 0 := by rw [mul_sub, mul_one, hε.eq, sub_self]
    have : ε * (ε - 1) ∈ 𝔪.asIdeal := by rw [h0]; exact 𝔪.asIdeal.zero_mem
    exact (hprime.mem_or_mem this).resolve_left hεm
  have hεe : ε * e = e := by
    have := (hann (ε - 1)).mpr hε1
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this

  obtain ⟨a', i, hi, hai⟩ := 𝔪.isMaximal.exists_inv ha

  refine ⟨𝔪, e, a', he, hem, hann, h1e, ?_, hεe⟩
  have hkey : (a' * a - 1) * e = 0 := by
    rw [hann]
    have : a' * a - 1 = -i := by rw [← hai]; ring
    rw [this]
    exact 𝔪.asIdeal.neg_mem hi
  calc a * ε * (a' * e) = ε * ((a' * a) * e) := by ring
    _ = ε * ((a' * a - 1) * e + e) := by ring
    _ = ε * e := by rw [hkey, zero_add]
    _ = e := hεe

end IsArtinianRing

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

open scoped TensorProduct

end ModularCurve.NonTriv

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinTorsionBar heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg baseChangeHom tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_tmul rationalHeckeRep rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra moduleFinite_padicInt_tateModule_jZero rationalTateModule_false_of_inertia_fixed_eigenplane heckeOperatorsCommuteBar ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar rationalRankTwoCyclotomic_family tateModule_rep_comp_tateHeckeRep_comm isReduced_rationalHeckeAlgebra smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace NonTriv
p2m_open "ModularCurve~TateModule"

open scoped TensorProduct

theorem plane_facts {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (hzw : ∀ z w : R, z * w = w * z) (b : Module.Basis (Fin 2) R V) (e : R) (c : Fin 2 → V)
    (hc : ∀ i, c i = e • b i) :
    (∀ v : V, e • v = v → v = b.repr v 0 • c 0 + b.repr v 1 • c 1) ∧
    (∀ g : V →+ V, (∀ (z : R) (v : V), g (z • v) = z • g v) →
      ∀ j : Fin 2, g (c j) = b.repr (g (b j)) 0 • c 0 + b.repr (g (b j)) 1 • c 1) ∧
    (∀ k : Fin 2 → R, k 0 • c 0 + k 1 • c 1 = 0 → ∀ i : Fin 2, k i * e = 0) ∧
    (∀ z : R, z * e = 0 → ∀ i : Fin 2, z • c i = 0) ∧
    (∀ x y : R, x * y = e → ∀ i : Fin 2, x • y • b i = c i) := by
  have hswap : ∀ (z w : R) (v : V), z • w • v = w • z • v := fun z w v => by
    rw [← mul_smul, hzw, mul_smul]
  refine ⟨fun v hev => ?_, fun g hg j => ?_, fun k hk i => ?_, fun z hz i => ?_, fun x y hxy i => ?_⟩
  · calc v = e • v := hev.symm
      _ = e • ∑ i : Fin 2, b.repr v i • b i := by rw [b.sum_repr]
      _ = b.repr v 0 • c 0 + b.repr v 1 • c 1 := by
          rw [Fin.sum_univ_two, smul_add, hswap e (b.repr v 0), hswap e (b.repr v 1), hc, hc]
  · rw [hc j, hg]
    conv_lhs => rw [← b.sum_repr (g (b j))]
    rw [Fin.sum_univ_two, smul_add, hswap e, hswap e, hc, hc]
  · have hk' : ∑ i : Fin 2, (k i * e) • b i = 0 := by
      rw [Fin.sum_univ_two, mul_smul, mul_smul, ← hc, ← hc]; exact hk
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => k i * e) hk' i
  · rw [hc, ← mul_smul, hz, zero_smul]
  · rw [hc, ← mul_smul, hxy]

set_option maxHeartbeats 64000000 in

theorem exists_package (p : ℕ) [Fact p.Prime] [Module HeckeAlg (JZero p)]
    (hred : IsReduced ↥(rationalHeckeAlgebra 2 (JZero p)))
    (a ε : ↥(rationalHeckeAlgebra 2 (JZero p))) (hε : ε * ε = ε) (h : a * ε ≠ 0) :
    ∃ (𝔪 : Ideal ↥(rationalHeckeAlgebra 2 (JZero p))) (e a' : ↥(rationalHeckeAlgebra 2 (JZero p))),
      (letI := instCommRingA p; 𝔪.IsMaximal) ∧ e * e = e ∧ e ∉ 𝔪 ∧
      (∀ z : ↥(rationalHeckeAlgebra 2 (JZero p)), z * e = 0 ↔ z ∈ 𝔪) ∧
      (∀ v : RationalTateModule 2 (JZero p), (∀ z ∈ 𝔪, z • v = 0) → e • v = v) ∧
      a * ε * (a' * e) = e ∧ ε * e = e ∧
      (∀ z w : ↥(rationalHeckeAlgebra 2 (JZero p)), z * w = w * z) := by
  letI := instCommRingA p
  haveI := isArtinianRing_A p
  haveI := hred
  obtain ⟨𝔪, e, a', he, he𝔪, hkey, h1e, haa'e, hεe⟩ :=
    IsArtinianRing.exists_primitive_idempotent_package a ε hε h
  refine ⟨𝔪.asIdeal, e, a', 𝔪.isMaximal, he.eq, he𝔪, hkey, fun v hv => ?_, haa'e, hεe, fun z w => mul_comm z w⟩
  have h0 : ((1 - e : ↥(rationalHeckeAlgebra 2 (JZero p))) : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v = 0 :=
    hv _ h1e
  rw [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0.symm

set_option linter.unusedVariables false in
set_option maxHeartbeats 32000000 in

theorem main (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∀ α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t),
      (∃ x : _root_.TateModule 2 (JZero p),
        (∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M) ∧ α x ≠ 0) →
      ∃ σ ∈ B.inertiaSubgroupIn ℚ, ∃ x : _root_.TateModule 2 (JZero p),
        (∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M) ∧
        _root_.TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (α x) ≠ α x := by
  letI := heckeModuleBar p
  intro α hα hx
  obtain ⟨x₀, hx₀, hαx₀⟩ := hx
  refine Classical.by_contradiction fun hcon => ?_
  have hneg : ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ x : _root_.TateModule 2 (JZero p),
      (∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M) →
      _root_.TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (α x) = α x := by
    intro σ hσ x hx
    by_contra h
    exact hcon ⟨σ, hσ, x, hx, h⟩

  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := ModularCurve.moduleFinite_padicInt_tateModule_jZero p 2
  haveI := noZeroSMulDivisors_tateModule p
  have hfdA := finiteDimensional_A p
  have hred : IsReduced ↥(rationalHeckeAlgebra 2 (JZero p)) := ModularCurve.isReduced_rationalHeckeAlgebra p 2
  haveI hcJ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero p) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar p (ModularCurve.heckeOperatorsCommuteBar p)

  obtain ⟨te, _h1, h2, h3, h4⟩ :=
    ModularCurve.exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar p
  have hT : Tower p te := ⟨h2, h3, h4⟩
  have hEA₀ := eisProj_mem_adjoin p hT
  have hEE : eisProj hT * eisProj hT = eisProj hT :=
    LinearMap.ext fun x => by rw [Module.End.mul_apply]; exact eisProj_idem hT x

  obtain ⟨a, ha⟩ : ∃ a : ↥(rationalHeckeAlgebra 2 (JZero p)),
      (a : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) = α.baseChange ℚ_[2] :=
    ⟨⟨_, baseChange_mem_rationalHeckeAlgebra p hα⟩, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ↥(rationalHeckeAlgebra 2 (JZero p)),
      (ε : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) = (eisProj hT).baseChange ℚ_[2] :=
    ⟨⟨_, baseChange_mem_rationalHeckeAlgebra p hEA₀⟩, rfl⟩
  have smul_def : ∀ (f : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)),
      f • v = (f : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v := fun _ _ => rfl
  have hx₀E : eisProj hT x₀ = x₀ := eisProj_eq_self hT x₀ hx₀
  have hv₀ : ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (α x₀) : RationalTateModule 2 (JZero p)) ≠ 0 := by
    intro h0
    apply hαx₀
    apply one_tmul_injective p
    show ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (α x₀) : RationalTateModule 2 (JZero p)) =
      (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (0 : _root_.TateModule 2 (JZero p))
    rw [h0, TensorProduct.tmul_zero]
  have haε : (a * ε) • ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] x₀ : RationalTateModule 2 (JZero p)) =
      (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (α x₀) := by
    rw [mul_smul, smul_def ε, hε, baseChange_one_tmul, hx₀E, smul_def a, ha, baseChange_one_tmul]
  have haε0 : a * ε ≠ 0 := fun h => hv₀ (by rw [← haε, h, zero_smul])
  have hεidem : ε * ε = ε := by
    refine Subtype.ext ?_
    rw [Subalgebra.coe_mul, hε, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hEE]

  obtain ⟨𝔪, e, a', h𝔪max, _hee, _he𝔪, key, hev, haa'e, _hεe, hzw⟩ :=
    exists_package p hred a ε hεidem haε0

  obtain ⟨b, hb⟩ := ModularCurve.rationalRankTwoCyclotomic_family p 2 hp.pos Nat.prime_two
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 → RationalTateModule 2 (JZero p), ∀ i, c i = e • b i := ⟨_, fun _ => rfl⟩
  have hgen : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlg),
      rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ∘ₗ rationalHeckeRep 2 (JZero p) t =
        rationalHeckeRep 2 (JZero p) t ∘ₗ rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ :=
    fun σ t => (ModularCurve.tateModule_rep_comp_tateHeckeRep_comm p 2 σ t).2
  have hcomm := rationalGaloisRep_smul_comm p hgen

  obtain ⟨hspan, hgal, hind, htors, hprod⟩ := plane_facts hzw b e c hc

  have hINDEP : ∀ k : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)),
      k 0 • c 0 + k 1 • c 1 = 0 → k 0 ∈ 𝔪 ∧ k 1 ∈ 𝔪 :=
    fun k hk => ⟨(key _).mp (hind k hk 0), (key _).mp (hind k hk 1)⟩

  have hTORS : ∀ z ∈ 𝔪, ∀ i : Fin 2, z • c i = 0 := fun z hz i => htors z ((key z).mpr hz) i

  have hSPAN : ∀ v : RationalTateModule 2 (JZero p), (∀ z ∈ 𝔪, z • v = 0) →
      ∃ k : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), v = k 0 • c 0 + k 1 • c 1 :=
    fun v hv => ⟨fun i => b.repr v i, hspan v (hev v hv)⟩

  have hSF : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ m : Fin 2 → Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)),
        (∀ j : Fin 2, rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c j) =
          m j 0 • c 0 + m j 1 • c 1) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ p * 2 → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
          A'.IsFrobeniusAt σ ℓ → m 0 0 * m 1 1 - m 1 0 * m 0 1 = (ℓ : ↥(rationalHeckeAlgebra 2 (JZero p)))) :=
    fun σ => ⟨fun j i => b.repr (rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b j)) i,
      fun j => hgal (rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).toAddMonoidHom
        (hcomm σ) j,
      fun ℓ hℓ hℓd A' hA' hσ => hb ℓ hℓ hℓd A' hA' σ hσ⟩

  have hFIX : ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ i : Fin 2,
      rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c i) = c i := by
    intro σ hσ i
    have hfixαE : ∀ v : RationalTateModule 2 (JZero p),
        rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ((α * eisProj hT).baseChange ℚ_[2] v) =
          (α * eisProj hT).baseChange ℚ_[2] v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul q y =>
          rw [LinearMap.baseChange_tmul, rationalGaloisRep_tmul, Module.End.mul_apply,
            hneg σ hσ _ (isEis_eisProj hT y)]
      | add v w hv hw => rw [map_add, map_add, hv, hw]
    have hprod' : (a * ε : ↥(rationalHeckeAlgebra 2 (JZero p))) • ((a' * e) • b i) = c i := hprod _ _ haa'e i
    have hcoe : ∀ v, (a * ε : ↥(rationalHeckeAlgebra 2 (JZero p))) • v = (α * eisProj hT).baseChange ℚ_[2] v := by
      intro v
      rw [smul_def, Subalgebra.coe_mul, ha, hε, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp,
        ← Module.End.mul_eq_comp]
    rw [← hprod', hcoe, hfixαE]
  exact ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane p B hB hfdA hcomm hzw 𝔪
    h𝔪max c hINDEP hTORS hSPAN hSF hFIX

end ModularCurve.NonTriv

theorem solution (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∀ α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t),
      (∃ x : _root_.TateModule 2 (JZero p),
        (∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M) ∧ α x ≠ 0) →
      ∃ σ ∈ B.inertiaSubgroupIn ℚ, ∃ x : _root_.TateModule 2 (JZero p),
        (∀ n : ℕ, ∃ M : ℕ, (x : ℕ → JZero p) n ∈ eisensteinTorsionBar p 2 M) ∧
        _root_.TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (α x) ≠ α x :=
  ModularCurve.NonTriv.main p B hB

end S_ModularCurve_exists_mem_inertiaSubgroupIn_tateModule_rep_ne_of_adjoin_tateHeckeRep_apply_ne_zero
end P2MW
export P2MW.S_ModularCurve_exists_mem_inertiaSubgroupIn_tateModule_rep_ne_of_adjoin_tateHeckeRep_apply_ne_zero (solution)
