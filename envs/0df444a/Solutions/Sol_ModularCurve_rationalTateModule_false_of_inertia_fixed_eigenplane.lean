-- Prove2me | solution 1 for ModularCurve.rationalTateModule_false_of_inertia_fixed_eigenplane
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/23e4ad83-4659-5f1e-b65a-9771ad40b046

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_eigenPlane_det_congruent_cyclotomic_of_frobenius_det
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
import Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_PadicInt_exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional
import Theorems.Thm_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable
import Theorems.Thm_exists_residueField_of_isMaximal_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.PhiGen.instNeZeroPhiGenCosetA CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath"
p2m_attr_erase "simp" "ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply"
p2m_attr_erase "simp" "JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 16000000

p2m_open "ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve IsLocalRing TensorProduct P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.TensorProduct"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar modularFunctionFieldBar JZero HeckeAlg RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeAlgebra JZeroTorsionFinite TateModule TateModule.mem_iff TateModule.pow_smul_apply JZero.exists_finiteDimensional_fixingSubgroup_smul_eq jZeroTorsionFinite"
namespace NonTriv
p2m_open "ModularCurve"

section prelim
variable (p : ℕ) [Fact p.Prime] [Module HeckeAlg (JZero p)]

omit [Fact p.Prime] in
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

end prelim

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 3200000

local notation "G" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section SecA

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Algebra ℤ_[2] O]

def rhoM : G →* Module.End O (O ⊗[ℤ_[2]] _root_.TateModule 2 (JZero p)) where
  toFun σ := (TateModule.rep 2 (JZero p) G σ).baseChange O
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_one ℤ_[2] (_root_.TateModule 2 (JZero p))
  map_mul' σ τ := by
    rw [map_mul]
    exact LinearMap.baseChange_mul _ _

theorem rhoM_apply (σ : G) : rhoM p O σ = (TateModule.rep 2 (JZero p) G σ).baseChange O := rfl

theorem rhoM_tmul (σ : G) (x y : _root_.TateModule 2 (JZero p))
    (h : (y : ℕ → JZero p) = σ • (x : ℕ → JZero p)) (b : O) :
    rhoM p O σ (b ⊗ₜ[ℤ_[2]] x) = b ⊗ₜ[ℤ_[2]] y := by
  rw [rhoM_apply, LinearMap.baseChange_tmul]
  congr 1
  refine Subtype.ext (funext fun n => ?_)
  rw [TateModule.rep_apply, h, Pi.smul_apply]

theorem smul_apply_toZModPow (a : ℤ_[2]) (x : _root_.TateModule 2 (JZero p)) (n : ℕ) :
    ((a • x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n = (PadicInt.toZModPow n a).val • (x : ℕ → JZero p) n := by
  rw [TateModule.smul_apply, TateModule.toZModPow_eq_appr, ZMod.val_natCast,
    Nat.mod_eq_of_lt (PadicInt.appr_lt a n), natCast_zsmul]

end SecA

section Bridge

variable (p : ℕ) [Fact p.Prime]

def epsFun (x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : _root_.TateModule 2 (JZero p) :=
  ⟨(x : ℕ → JZero p), fun n =>
    ⟨by
      letI := heckeModuleBar p
      have h := ModularCurve.TateModule.pow_smul_apply x.2 n
      rwa [← natCast_zsmul] at h,
     by
      letI := heckeModuleBar p
      have h := (ModularCurve.TateModule.mem_iff.mp x.2).2 n
      rwa [← natCast_zsmul] at h⟩⟩

def epsInv (x : _root_.TateModule 2 (JZero p)) : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) :=
  letI := heckeModuleBar p
  ⟨(x : ℕ → JZero p), ModularCurve.TateModule.mem_iff.mpr
    ⟨_root_.TateModule.apply_zero x, fun n => by
      have h := _root_.TateModule.compat x n
      rwa [natCast_zsmul] at h⟩⟩

def epsAdd : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) ≃+ _root_.TateModule 2 (JZero p) where
  toFun := epsFun p
  invFun := epsInv p
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

@[scoped simp] theorem coe_epsAdd (x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) :
    ((epsAdd p x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) = (x : ℕ → JZero p) := rfl

@[scoped simp] theorem coe_epsAdd_symm (x : _root_.TateModule 2 (JZero p)) :
    (((epsAdd p).symm x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : ℕ → JZero p) =
      (x : ℕ → JZero p) := rfl

def smulES : SMul ℤ_[2] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) :=
  ⟨fun a x => (epsAdd p).symm (a • epsAdd p x)⟩

@[reducible] def moduleES : Module ℤ_[2] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) :=
  letI := smulES p
  Function.Injective.module ℤ_[2] (epsAdd p).toAddMonoidHom (epsAdd p).injective fun a x => by
    show epsAdd p ((epsAdd p).symm (a • epsAdd p x)) = a • epsAdd p x
    exact AddEquiv.apply_symm_apply _ _

def eps : letI := moduleES p;
    ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) ≃ₗ[ℤ_[2]] _root_.TateModule 2 (JZero p) :=
  letI := moduleES p
  { epsAdd p with
    map_smul' := fun a x => by
      show epsAdd p ((epsAdd p).symm (a • epsAdd p x)) = a • epsAdd p x
      rw [AddEquiv.apply_symm_apply] }

theorem eps_apply (x) : (letI := moduleES p; eps p x) = epsAdd p x := rfl

theorem smul_apply_toZModPow_ES (a : ℤ_[2]) (x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) (n : ℕ) :
    letI := moduleES p
    ((a • x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : ℕ → JZero p) n =
      (PadicInt.toZModPow n a).val • (x : ℕ → JZero p) n := by
  show (((epsAdd p).symm (a • epsAdd p x) : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : ℕ → JZero p) n = _
  rw [coe_epsAdd_symm, smul_apply_toZModPow p, coe_epsAdd]

end Bridge

section ContES

variable (p : ℕ) [Fact p.Prime]

def repES : letI := moduleES p;
    G →* Module.End ℤ_[2] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)) :=
  letI := moduleES p
  { toFun := fun σ => (eps p).symm.toLinearMap ∘ₗ TateModule.rep 2 (JZero p) G σ ∘ₗ (eps p).toLinearMap
    map_one' := by
      refine LinearMap.ext fun x => ?_
      simp only [map_one, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.End.one_apply,
        LinearEquiv.symm_apply_apply]
    map_mul' := fun σ τ => by
      refine LinearMap.ext fun x => ?_
      simp only [map_mul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.End.mul_apply,
        LinearEquiv.apply_symm_apply] }

theorem coe_repES_apply (σ : G) (x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) :
    (letI := moduleES p; ((repES p σ x : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : ℕ → JZero p))
      = σ • (x : ℕ → JZero p) := by
  funext n
  show (((epsAdd p).symm (TateModule.rep 2 (JZero p) G σ (epsAdd p x)) : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) : ℕ → JZero p) n = _
  rw [coe_epsAdd_symm, TateModule.rep_apply, coe_epsAdd, Pi.smul_apply]

variable (O : Type) [CommRing O] [Algebra ℤ_[2] O]

def rhoMES : letI := moduleES p;
    G →* Module.End O (O ⊗[ℤ_[2]] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) :=
  letI := moduleES p
  { toFun := fun σ => (repES p σ).baseChange O
    map_one' := by rw [map_one]; exact LinearMap.baseChange_one ℤ_[2] _
    map_mul' := fun σ τ => by rw [map_mul]; exact LinearMap.baseChange_mul _ _ }

theorem rhoMES_apply (σ : G) : (letI := moduleES p; rhoMES p O σ = (repES p σ).baseChange O) := rfl

theorem rhoMES_tmul (σ : G) (x y : ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)))
    (h : (y : ℕ → JZero p) = σ • (x : ℕ → JZero p)) (b : O) :
    (letI := moduleES p; rhoMES p O σ (b ⊗ₜ[ℤ_[2]] x) = b ⊗ₜ[ℤ_[2]] y) := by
  letI := moduleES p
  rw [rhoMES_apply, LinearMap.baseChange_tmul]
  congr 1
  exact Subtype.ext ((coe_repES_apply p σ x).trans h.symm)

end ContES

section Cont

variable (p : ℕ) [Fact p.Prime]

theorem finite_torsionBy (n : ℕ) : Finite ↥(Submodule.torsionBy ℤ (JZero p) ((2 ^ n : ℕ) : ℤ)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h : JZeroTorsionFinite p (2 ^ n) := jZeroTorsionFinite p (2 ^ n) (Nat.pos_of_ne_zero (by positivity))
  haveI : Finite ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (2 ^ n)) := h

  exact Finite.of_injective
    (fun z : ↥(Submodule.torsionBy ℤ (JZero p) ((2 ^ n : ℕ) : ℤ)) =>
      (⟨z.1, z.2⟩ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (2 ^ n))))
    (fun a b h => Subtype.ext (congrArg Subtype.val h))

theorem exists_level (n : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : G, (∀ x ∈ L, σ x = x) →
        ∀ z ∈ Submodule.torsionBy ℤ (JZero p) ((2 ^ n : ℕ) : ℤ), σ • z = z := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := finite_torsionBy p n
  choose L₀ hfd hfix using fun z : ↥(Submodule.torsionBy ℤ (JZero p) ((2 ^ n : ℕ) : ℤ)) =>
    JZero.exists_finiteDimensional_fixingSubgroup_smul_eq p (z : JZero p)
  refine ⟨⨆ z, L₀ z, ?_, fun σ hσ z hz => ?_⟩
  · haveI : ∀ z, FiniteDimensional ℚ (L₀ z) := hfd
    exact IntermediateField.finiteDimensional_iSup_of_finite
  · have hmem : σ ∈ (L₀ ⟨z, hz⟩).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hσ x (le_iSup L₀ ⟨z, hz⟩ hx)
    exact hfix ⟨z, hz⟩ σ hmem

variable (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[2] O]

theorem rhoMES_isAdicContinuous (h2 : (2 : O) ∈ maximalIdeal O) :
    (letI := moduleES p; GaloisActionIsAdicContinuous O (rhoMES p O)) := by
  letI := moduleES p
  letI := heckeModuleBar p
  intro n
  obtain ⟨L, hL, hfix⟩ := exists_level p n
  refine ⟨L, hL, fun σ hσ v => ?_⟩

  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | add v w hv hw => rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ hv hw
  | tmul b x =>

    have hlev : σ • ((eps p x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n =
        ((eps p x : _root_.TateModule 2 (JZero p)) : ℕ → JZero p) n := by
      apply hfix σ hσ
      rw [Submodule.mem_torsionBy_iff]
      exact _root_.TateModule.torsion (eps p x) n
    have hroot := _root_.TateModule.rep_sub_mem_of_apply_eq σ (eps p x) n hlev
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hroot
    obtain ⟨y, -, hy⟩ := hroot

    have hES : repES p σ x - x = (eps p).symm ((((2 : ℕ) : ℤ_[2]) ^ n) • y) := by
      rw [hy, map_sub, LinearEquiv.symm_apply_apply]
      rfl

    rw [rhoMES_apply, LinearMap.baseChange_tmul]
    have e1 : b ⊗ₜ[ℤ_[2]] (repES p σ x) - b ⊗ₜ[ℤ_[2]] x = b ⊗ₜ[ℤ_[2]] (repES p σ x - x) := by
      first
        | simp only [TensorProduct.tmul_sub]
        | exact (map_sub (TensorProduct.mk ℤ_[2] O _ b) (repES p σ x) x).symm
    rw [e1, hES, map_smul, ← TensorProduct.smul_tmul, Algebra.smul_def]
    have h2n : algebraMap ℤ_[2] O (((2 : ℕ) : ℤ_[2]) ^ n) * b ∈ maximalIdeal O ^ n := by
      rw [map_pow, map_natCast, Nat.cast_ofNat]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h2 n)
    have e2 : ((algebraMap ℤ_[2] O (((2 : ℕ) : ℤ_[2]) ^ n) * b) ⊗ₜ[ℤ_[2]] (eps p).symm y :
        O ⊗[ℤ_[2]] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)))
          = (algebraMap ℤ_[2] O (((2 : ℕ) : ℤ_[2]) ^ n) * b) • ((1 : O) ⊗ₜ[ℤ_[2]] (eps p).symm y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e2]
    exact Submodule.smul_mem_smul h2n Submodule.mem_top

end Cont

section Phi

variable (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[2] O] [Field K] [Algebra O K]
  [Algebra ℤ_[2] K] [Algebra ℚ_[2] K] [IsScalarTower ℤ_[2] O K] [IsScalarTower ℤ_[2] ℚ_[2] K]

def Phi : letI := moduleES p;
    K ⊗[ℚ_[2]] RationalTateModule 2 (JZero p) ≃ₗ[K]
      K ⊗[O] (O ⊗[ℤ_[2]] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))) :=
  letI := moduleES p
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[2] ℚ_[2] K K (_root_.TateModule 2 (JZero p))).trans
    ((LinearEquiv.baseChange ℤ_[2] K _ _ (eps p).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[2] O K K
        ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p))).symm)

theorem Phi_tmul (k : K) (q : ℚ_[2]) (x : _root_.TateModule 2 (JZero p)) :
    (letI := moduleES p;
      Phi p O K (k ⊗ₜ[ℚ_[2]] (q ⊗ₜ[ℤ_[2]] x)) = (q • k) ⊗ₜ[O] ((1 : O) ⊗ₜ[ℤ_[2]] (eps p).symm x)) := by
  letI := moduleES p
  simp only [Phi, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    LinearEquiv.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

theorem Phi_natural (f : _root_.TateModule 2 (JZero p) →ₗ[ℤ_[2]] _root_.TateModule 2 (JZero p))
    (w : K ⊗[ℚ_[2]] RationalTateModule 2 (JZero p)) :
    (letI := moduleES p;
      Phi p O K (((f.baseChange ℚ_[2]).baseChange K) w) =
        ((((eps p).symm.toLinearMap ∘ₗ f ∘ₗ (eps p).toLinearMap).baseChange O).baseChange K) (Phi p O K w)) := by
  letI := moduleES p
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul k v =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
    | tmul q x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Phi_tmul, Phi_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]

end Phi

end ModularCurve.NonTriv
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve"

namespace TensorProduct
p2m_export "TensorProduct" "AlgebraTensorModule.cancelBaseChange_tmul AlgebraTensorModule.cancelBaseChange_symm_tmul congr AlgebraTensorModule.lift tmul_zero smul_tmul' smul_tmul lift mk ext tmul_sub tmul map Algebra.smul_def tmul_add AlgebraTensorModule.cancelBaseChange mulMap_injOn_and_surjOn_diagonal_of_isSeparable"
namespace DiagEigen
p2m_open "TensorProduct"

variable (F K P : Type*) [Field F] [Field K] [Algebra F K]
  [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P]

noncomputable def rightSMul (k : K) : K ⊗[F] P →ₗ[K] K ⊗[F] P :=
  LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F)

theorem rightSMul_tmul (k a : K) (v : P) : rightSMul F K P k (a ⊗ₜ[F] v) = a ⊗ₜ[F] (k • v) := by
  simp [rightSMul]

noncomputable def diag : Submodule K (K ⊗[F] P) where
  carrier := {w | ∀ k : K, k • w = rightSMul F K P k w}
  add_mem' := by
    intro a b ha hb k
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [smul_add, map_add, ha k, hb k]
  zero_mem' := by intro k; simp
  smul_mem' := by
    intro c w hw k
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [smul_comm, hw k, map_smul]

theorem mem_diag {w : K ⊗[F] P} : w ∈ diag F K P ↔ ∀ k : K, k • w = rightSMul F K P k w := Iff.rfl

noncomputable def mulMap : K ⊗[F] P →ₗ[K] P :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul K P : K →ₗ[K] P →ₗ[K] P).flip.restrictScalars F |>.flip)

theorem mulMap_tmul (a : K) (v : P) : mulMap F K P (a ⊗ₜ[F] v) = a • v := by
  simp [mulMap]

theorem baseChange_mem_diag (g : P →ₗ[K] P) {w : K ⊗[F] P} (hw : w ∈ diag F K P) :
    (g.restrictScalars F).baseChange K w ∈ diag F K P := by
  intro k
  have hcomm : (g.restrictScalars F).baseChange K ∘ₗ rightSMul F K P k =
      rightSMul F K P k ∘ₗ (g.restrictScalars F).baseChange K := by
    simp only [rightSMul, ← LinearMap.baseChange_comp]
    congr 1
    ext v
    simp
  rw [← map_smul, hw k, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]

theorem mulMap_baseChange (g : P →ₗ[K] P) (w : K ⊗[F] P) :
    mulMap F K P ((g.restrictScalars F).baseChange K w) = g (mulMap F K P w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp [map_add, hu, hv]
  | tmul a v => rw [LinearMap.baseChange_tmul, mulMap_tmul, mulMap_tmul]; simp

end TensorProduct.DiagEigen
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar modularFunctionFieldBar JZero HeckeAlg RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeAlgebra JZeroTorsionFinite TateModule TateModule.mem_iff TateModule.pow_smul_apply JZero.exists_finiteDimensional_fixingSubgroup_smul_eq jZeroTorsionFinite"
namespace NonTriv
p2m_open "ModularCurve"

local notation "G" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Plane

variable (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[2] O] [Field K] [Algebra O K]
  [Algebra ℤ_[2] K] [Algebra ℚ_[2] K] [IsScalarTower ℤ_[2] O K] [IsScalarTower ℤ_[2] ℚ_[2] K]
  (j : (Fin 2 → K) →ₗ[ℚ_[2]] RationalTateModule 2 (JZero p))

def Wplane : letI := moduleES p;
    Submodule K (K ⊗[O] (O ⊗[ℤ_[2]] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)))) :=
  letI := moduleES p
  (TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K)).map ((Phi p O K).toLinearMap ∘ₗ j.baseChange K)

theorem mem_Wplane_iff {w} : (letI := moduleES p; w ∈ Wplane p O K j ↔
    ∃ e ∈ TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K), Phi p O K (j.baseChange K e) = w) := by
  letI := moduleES p
  simp only [Wplane, Submodule.mem_map, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]

theorem exists_diagEquiv [FiniteDimensional ℚ_[2] K] [Algebra.IsSeparable ℚ_[2] K] :
    ∃ πE : ↥(TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K)) ≃ₗ[K] (Fin 2 → K),
      ∀ e, πE e = TensorProduct.DiagEigen.mulMap ℚ_[2] K (Fin 2 → K) e := by
  obtain ⟨hinj, hsurj⟩ := TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable
    (F := ℚ_[2]) (K := K) (P := Fin 2 → K) (TensorProduct.DiagEigen.mulMap ℚ_[2] K (Fin 2 → K))
    (TensorProduct.DiagEigen.mulMap_tmul ℚ_[2] K (Fin 2 → K))
  refine ⟨LinearEquiv.ofBijective ((TensorProduct.DiagEigen.mulMap ℚ_[2] K (Fin 2 → K)).domRestrict _) ⟨?_, ?_⟩,
    fun e => rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨w, hw⟩ h
    exact Subtype.ext (hinj w hw h)
  · intro v
    obtain ⟨w, hw, hv⟩ := hsurj v
    exact ⟨⟨w, hw⟩, hv⟩

theorem finrank_Wplane [FiniteDimensional ℚ_[2] K] [Algebra.IsSeparable ℚ_[2] K] (hj : Function.Injective j) :
    (letI := moduleES p; Module.finrank K (Wplane p O K j) = 2) := by
  letI := moduleES p
  have hinj : Function.Injective ((Phi p O K).toLinearMap ∘ₗ j.baseChange K) := by
    rw [LinearMap.coe_comp]
    refine (Phi p O K).injective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap j hj
  obtain ⟨πE, -⟩ := exists_diagEquiv K
  rw [Wplane, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, πE.finrank_eq, Module.finrank_fin_fun]

theorem Wplane_stable (σ : G) (g : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
    (hg : rationalGaloisRep 2 (JZero p) G σ ∘ₗ j = j ∘ₗ g.restrictScalars ℚ_[2]) :
    (letI := moduleES p; ∀ w ∈ Wplane p O K j,
      (rhoMES p O σ).baseChange K w ∈ Wplane p O K j ∧
      ∀ e ∈ TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K), Phi p O K (j.baseChange K e) = w →
        (rhoMES p O σ).baseChange K w =
          Phi p O K (j.baseChange K ((g.restrictScalars ℚ_[2]).baseChange K e))) := by
  letI := moduleES p

  have key : ∀ e, (rhoMES p O σ).baseChange K (Phi p O K (j.baseChange K e)) =
      Phi p O K (j.baseChange K ((g.restrictScalars ℚ_[2]).baseChange K e)) := by
    intro e
    have h1 := Phi_natural p O K (_root_.TateModule.rep 2 (JZero p) G σ) (j.baseChange K e)
    have h2 : ((_root_.TateModule.rep 2 (JZero p) G σ).baseChange ℚ_[2]).baseChange K (j.baseChange K e) =
        j.baseChange K ((g.restrictScalars ℚ_[2]).baseChange K e) := by
      rw [← rationalGaloisRep_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hg,
        LinearMap.baseChange_comp, LinearMap.comp_apply]
    rw [h2] at h1
    exact h1.symm
  intro w hw
  obtain ⟨e, he, rfl⟩ := (mem_Wplane_iff p O K j).mp hw
  refine ⟨?_, fun e' he' h => ?_⟩
  · rw [key]
    exact (mem_Wplane_iff p O K j).mpr ⟨_, TensorProduct.DiagEigen.baseChange_mem_diag ℚ_[2] K (Fin 2 → K) g he, rfl⟩
  · rw [← h, key]

end Plane
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

section Det

variable (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[2] O] [Field K] [Algebra O K]
  [Algebra ℤ_[2] K] [Algebra ℚ_[2] K] [IsScalarTower ℤ_[2] O K] [IsScalarTower ℤ_[2] ℚ_[2] K]
  [FiniteDimensional ℚ_[2] K] [Algebra.IsSeparable ℚ_[2] K]
  (j : (Fin 2 → K) →ₗ[ℚ_[2]] RationalTateModule 2 (JZero p)) (hj : Function.Injective j)

include hj in

theorem exists_conj_Wplane (σ : G) (g : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
    (hg : rationalGaloisRep 2 (JZero p) G σ ∘ₗ j = j ∘ₗ g.restrictScalars ℚ_[2]) :
    (letI := moduleES p;
      ∃ Ψ : (Fin 2 → K) ≃ₗ[K] ↥(Wplane p O K j), ∀ u : Fin 2 → K,
        (rhoMES p O σ).baseChange K ((Ψ u : ↥(Wplane p O K j)) : _) = ((Ψ (g u) : ↥(Wplane p O K j)) : _)) := by
  letI := moduleES p
  have hinj : Function.Injective ((Phi p O K).toLinearMap ∘ₗ j.baseChange K) := by
    rw [LinearMap.coe_comp]
    refine (Phi p O K).injective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap j hj
  obtain ⟨πE, hπE⟩ := exists_diagEquiv K
  let θW := Submodule.equivMapOfInjective _ hinj (TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K))
  refine ⟨πE.symm.trans θW, fun u => ?_⟩
  have key := Wplane_stable p O K j σ g hg
  show (rhoMES p O σ).baseChange K (Phi p O K (j.baseChange K (πE.symm u : _))) =
    Phi p O K (j.baseChange K (πE.symm (g u) : _))
  have hmem := (πE.symm u).2
  rw [(key _ ((mem_Wplane_iff p O K j).mpr ⟨_, hmem, rfl⟩)).2 _ hmem rfl]
  congr 2
  have h1 : (g.restrictScalars ℚ_[2]).baseChange K (πE.symm u : _) =
      ((⟨_, TensorProduct.DiagEigen.baseChange_mem_diag ℚ_[2] K (Fin 2 → K) g hmem⟩ :
        ↥(TensorProduct.DiagEigen.diag ℚ_[2] K (Fin 2 → K))) : _) := rfl
  rw [h1]
  congr 1
  apply πE.injective
  rw [LinearEquiv.apply_symm_apply, hπE, TensorProduct.DiagEigen.mulMap_baseChange, ← hπE,
    LinearEquiv.apply_symm_apply]

end Det
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

section B1

variable (p : ℕ) [Fact p.Prime] [Module HeckeAlg (JZero p)]
variable (K : Type) [Field K] [Algebra ℚ_[2] K]
  (θ : ↥(rationalHeckeAlgebra 2 (JZero p)) →ₐ[ℚ_[2]] K)
  (c : Fin 2 → RationalTateModule 2 (JZero p))

omit [Fact p.Prime] in

theorem qsmul_smul (r : ℚ_[2]) (a : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) :
    (r • a) • v = r • (a • v) := by
  show ((r • a : ↥(rationalHeckeAlgebra 2 (JZero p))) : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v = _
  rw [Subalgebra.coe_smul, LinearMap.smul_apply]
  rfl

omit [Fact p.Prime] in
theorem add_smul' (a b : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) :
    (a + b) • v = a • v + b • v := by
  show ((a + b : ↥(rationalHeckeAlgebra 2 (JZero p))) : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v = _
  rw [Subalgebra.coe_add, LinearMap.add_apply]
  rfl

omit [Fact p.Prime] in
theorem mul_smul' (a b : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) :
    (a * b) • v = a • (b • v) := by
  show ((a * b : ↥(rationalHeckeAlgebra 2 (JZero p))) : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v = _
  rw [Subalgebra.coe_mul, Module.End.mul_apply]
  rfl

omit [Fact p.Prime] in
theorem smul_add' (a : ↥(rationalHeckeAlgebra 2 (JZero p))) (v w : RationalTateModule 2 (JZero p)) :
    a • (v + w) = a • v + a • w := by
  show ((a : ↥(rationalHeckeAlgebra 2 (JZero p))) : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) (v + w) = _
  rw [LinearMap.map_add]
  rfl

noncomputable def phiA : (Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) →ₗ[ℚ_[2]] RationalTateModule 2 (JZero p) where
  toFun b := b 0 • c 0 + b 1 • c 1
  map_add' b b' := by
    simp only [Pi.add_apply, add_smul']
    abel
  map_smul' r b := by
    simp only [Pi.smul_apply, qsmul_smul, smul_add, RingHom.id_apply]

omit [Fact p.Prime] in
theorem phiA_apply (b : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) : phiA p c b = b 0 • c 0 + b 1 • c 1 := rfl

noncomputable def Theta : (Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) →ₗ[ℚ_[2]] (Fin 2 → K) :=
  θ.toLinearMap.compLeft (Fin 2)

omit [Fact p.Prime] in
theorem Theta_apply (b : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) : Theta p K θ b = fun i => θ (b i) := rfl

variable (hθ : Function.Surjective θ)
include hθ

omit [Fact p.Prime] in
theorem Theta_surjective : Function.Surjective (Theta p K θ) := fun u =>
  ⟨fun i => Function.surjInv hθ (u i), funext fun i => Function.surjInv_eq hθ (u i)⟩

omit [Fact p.Prime] in
theorem exists_section : ∃ L : (Fin 2 → K) →ₗ[ℚ_[2]] (Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))),
    Theta p K θ ∘ₗ L = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (LinearMap.range_eq_top.mpr (Theta_surjective p K θ hθ))

noncomputable def secL : (Fin 2 → K) →ₗ[ℚ_[2]] (Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) :=
  (exists_section p K θ hθ).choose

omit [Fact p.Prime] in
theorem Theta_secL (u : Fin 2 → K) : Theta p K θ (secL p K θ hθ u) = u :=
  LinearMap.congr_fun (exists_section p K θ hθ).choose_spec u

variable (TORS : ∀ a : ↥(rationalHeckeAlgebra 2 (JZero p)), θ a = 0 → ∀ i, a • c i = 0)

include TORS in
omit [Fact p.Prime] in

theorem phiA_eq_zero_of_Theta (b : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) (hb : Theta p K θ b = 0) :
    phiA p c b = 0 := by
  have h : ∀ i, θ (b i) = 0 := fun i => congr_fun hb i
  rw [phiA_apply, TORS _ (h 0) 0, TORS _ (h 1) 1, add_zero]

noncomputable def jmap : (Fin 2 → K) →ₗ[ℚ_[2]] RationalTateModule 2 (JZero p) :=
  phiA p c ∘ₗ secL p K θ hθ

include TORS in
omit [Fact p.Prime] in

theorem jmap_eq (u : Fin 2 → K) (b : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) (hb : ∀ i, θ (b i) = u i) :
    jmap p K θ c hθ u = b 0 • c 0 + b 1 • c 1 := by
  have h1 : Theta p K θ (secL p K θ hθ u - b) = 0 := by
    rw [(map_sub (Theta p K θ) _ _ : Theta p K θ (secL p K θ hθ u - b) = _), Theta_secL, Theta_apply, sub_eq_zero]
    exact (funext hb).symm
  have h2 := phiA_eq_zero_of_Theta p K θ c hθ TORS _ h1
  rw [(map_sub (phiA p c) _ _ : phiA p c (secL p K θ hθ u - b) = _), sub_eq_zero] at h2
  show phiA p c (secL p K θ hθ u) = _
  rw [h2, phiA_apply]

attribute [irreducible] jmap phiA secL

include TORS in
omit [Fact p.Prime] in

theorem jmap_theta (a : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p))) :
    jmap p K θ c hθ (fun i => θ (a i)) = a 0 • c 0 + a 1 • c 1 :=
  jmap_eq p K θ c hθ TORS _ a (fun _ => rfl)

include TORS in
omit [Fact p.Prime] in

theorem jmap_injective
    (INDEP : ∀ a : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), a 0 • c 0 + a 1 • c 1 = 0 → θ (a 0) = 0 ∧ θ (a 1) = 0) :
    Function.Injective (jmap p K θ c hθ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  obtain ⟨b, hb⟩ := Theta_surjective p K θ hθ u
  have hb' : ∀ i, θ (b i) = u i := fun i => congr_fun hb i
  rw [jmap_eq p K θ c hθ TORS u b hb'] at hu
  obtain ⟨h0, h1⟩ := INDEP _ hu
  funext i
  fin_cases i
  · exact (hb' 0).symm.trans h0
  · exact (hb' 1).symm.trans h1

include TORS in
omit [Fact p.Prime] in

theorem jmap_smul (a : ↥(rationalHeckeAlgebra 2 (JZero p))) (u : Fin 2 → K) :
    jmap p K θ c hθ (θ a • u) = a • jmap p K θ c hθ u := by
  obtain ⟨b, hb⟩ := Theta_surjective p K θ hθ u
  have hb' : ∀ i, θ (b i) = u i := fun i => congr_fun hb i
  rw [jmap_eq p K θ c hθ TORS u b hb',
    jmap_eq p K θ c hθ TORS (θ a • u) (fun i => a * b i)
      (fun i => by rw [map_mul, hb' i]; rfl)]
  show (a * b 0) • c 0 + (a * b 1) • c 1 = a • (b 0 • c 0 + b 1 • c 1)
  exact (congrArg₂ (· + ·) (mul_smul' p a (b 0) (c 0)) (mul_smul' p a (b 1) (c 1))).trans
    (smul_add' p a _ _).symm

omit [Fact p.Prime] in

theorem smul_def' (x : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) :
    x • v = (x : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v := rfl

theorem coe_comm_apply (x y : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) :
    (x : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) ((y : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v)
      = (y : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) ((x : Module.End ℚ_[2] (RationalTateModule 2 (JZero p))) v) := by
  have hc : x * y = y * x := by
    letI := instCommRingA p
    exact mul_comm x y
  rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, hc, Subalgebra.coe_mul, Module.End.mul_apply]

omit [Fact p.Prime] hθ in

theorem galois_core {A' V' : Type*} [Ring A'] [AddCommGroup V'] (sm : A' → V' → V') (ρ : V' → V')
    (hρadd : ∀ v w, ρ (v + w) = ρ v + ρ w)
    (hadd : ∀ a b v, sm (a + b) v = sm a v + sm b v) (hmul : ∀ a b v, sm (a * b) v = sm a (sm b v))
    (hsmadd : ∀ a v w, sm a (v + w) = sm a v + sm a w)
    (hc : ∀ x y : A', x * y = y * x) (hcomm : ∀ a v, ρ (sm a v) = sm a (ρ v))
    (c' : Fin 2 → V') (M : Fin 2 → Fin 2 → A') (hM : ∀ j, ρ (c' j) = sm (M j 0) (c' 0) + sm (M j 1) (c' 1))
    (b : Fin 2 → A') :
    ρ (sm (b 0) (c' 0) + sm (b 1) (c' 1)) = sm (∑ j, M j 0 * b j) (c' 0) + sm (∑ j, M j 1 * b j) (c' 1) := by
  rw [hρadd, hcomm, hcomm, hM 0, hM 1, hsmadd, hsmadd, ← hmul, ← hmul, ← hmul, ← hmul,
    Fin.sum_univ_two, Fin.sum_univ_two, hadd, hadd, hc (M 0 0) (b 0), hc (M 1 0) (b 1), hc (M 0 1) (b 0),
    hc (M 1 1) (b 1)]
  abel

include TORS in

theorem jmap_galois
    (ρσ : RationalTateModule 2 (JZero p) →ₗ[ℚ_[2]] RationalTateModule 2 (JZero p))
    (hcomm : ∀ (a : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)), ρσ (a • v) = a • ρσ v)
    (M : Fin 2 → Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)))
    (hM : ∀ j : Fin 2, ρσ (c j) = M j 0 • c 0 + M j 1 • c 1) (u : Fin 2 → K) :
    ρσ (jmap p K θ c hθ u) = jmap p K θ c hθ (fun i => ∑ j, θ (M j i) * u j) := by
  obtain ⟨b, hb⟩ := Theta_surjective p K θ hθ u
  have hb' : ∀ i, θ (b i) = u i := fun i => congr_fun hb i
  rw [jmap_eq p K θ c hθ TORS u b hb',
    jmap_eq p K θ c hθ TORS (fun i => ∑ j, θ (M j i) * u j) (fun i => ∑ j, M j i * b j)
      (fun i => by simp only [map_sum, map_mul, hb'])]
  have hc : ∀ x y : ↥(rationalHeckeAlgebra 2 (JZero p)), x * y = y * x := fun x y => by
    letI := instCommRingA p
    exact mul_comm x y
  exact galois_core (fun (a : ↥(rationalHeckeAlgebra 2 (JZero p))) (v : RationalTateModule 2 (JZero p)) => a • v)
    ρσ (map_add ρσ) (add_smul' p) (mul_smul' p) (smul_add' p) hc hcomm c M hM b

end B1
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

section Endgame

variable (p : ℕ) [Fact p.Prime]

open IsLocalRing in

theorem false_of_inertia_trivial_on_plane
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharZero O] [Algebra ℤ_[2] O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (h2 : (2 : O) ∈ maximalIdeal O)
    (W : letI := moduleES p;
      Submodule K (K ⊗[O] (O ⊗[ℤ_[2]] ↥(letI := heckeModuleBar p; ModularCurve.TateModule 2 (JZero p)))))
    (hW2 : Module.finrank K W = 2)
    (hW : letI := moduleES p; ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (rhoMES p O σ).baseChange K w ∈ W)
    (hfrobdet : letI := moduleES p;
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ p → ℓ ∉ ({2} : Finset ℕ) →
        ∀ B' : ValuationSubring (AlgebraicClosure ℚ), B'.LiesOverPrime ℓ →
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B'.IsFrobeniusAt σ ℓ →
            LinearMap.det (M := ↥W) (((rhoMES p O σ).baseChange K).restrict (hW σ)) = (ℓ : K))
    (hfix : letI := moduleES p; ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ w ∈ W, (rhoMES p O σ).baseChange K w = w) :
    False := by
  letI := moduleES p
  letI := heckeModuleBar p
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have H := eigenPlane_det_congruent_cyclotomic_of_frobenius_det (M := p) 2 O K
    (smul_apply_toZModPow_ES p) ({2} : Finset ℕ) (rhoMES p O)
    (fun σ x y h b => rhoMES_tmul p O σ x y h b) (rhoMES_isAdicContinuous p O h2) W hW2 hW hfrobdet
  obtain ⟨σ₀, hσ₀, hζ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one B hB
  obtain ⟨d, hd, hd3⟩ := H σ₀ 2 3 (fun μ hμ => hζ μ (by simpa using hμ))

  have hid : ((rhoMES p O σ₀).baseChange K).restrict (hW σ₀) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨w, hw⟩
    apply Subtype.ext
    simp only [LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq]
    exact hfix σ₀ hσ₀ w hw
  rw [hid, LinearMap.det_id] at hd
  have hd1 : d = 1 := IsFractionRing.injective O K (by rw [hd, map_one])
  rw [hd1, Ideal.mem_span_singleton] at hd3
  obtain ⟨t, ht⟩ := hd3

  have h2t : (2 : O) * (2 * t + 1) = 0 := by
    have ht' := ht
    push_cast at ht'
    linear_combination -ht'
  have h21 : (2 : O) * t + 1 = 0 := by
    rcases mul_eq_zero.mp h2t with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hone : (1 : O) ∈ maximalIdeal O := by
    have : (1 : O) = 2 * (-t) := by linear_combination h21
    rw [this]
    exact Ideal.mul_mem_right _ _ h2
  exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

end Endgame
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

section Assembly

theorem det_toLin'_fin_two {K : Type} [Field K] (N : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.det (Matrix.toLin' N) = N 0 0 * N 1 1 - N 0 1 * N 1 0 := by
  rw [LinearMap.det_toLin', Matrix.det_fin_two]

theorem toLin'_apply_eq {K : Type} [Field K] (N : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) :
    Matrix.toLin' N u = fun i => ∑ j, N i j * u j := by
  rw [Matrix.toLin'_apply]
  rfl

set_option maxHeartbeats 32000000 in
theorem l5_main (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∀ (hfdA : FiniteDimensional ℚ_[2] ↥(rationalHeckeAlgebra 2 (JZero p)))
      (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ↥(rationalHeckeAlgebra 2 (JZero p)))
        (v : RationalTateModule 2 (JZero p)),
        rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (a • v) =
          a • rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
      (hmul : ∀ a b : ↥(rationalHeckeAlgebra 2 (JZero p)), a * b = b * a)
      (𝔪 : Ideal ↥(rationalHeckeAlgebra 2 (JZero p))), 𝔪.IsMaximal →
    ∀ (c : Fin 2 → RationalTateModule 2 (JZero p)),
      (∀ a : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), a 0 • c 0 + a 1 • c 1 = 0 → a 0 ∈ 𝔪 ∧ a 1 ∈ 𝔪) →
      (∀ a ∈ 𝔪, ∀ i : Fin 2, a • c i = 0) →
      (∀ v : RationalTateModule 2 (JZero p), (∀ a ∈ 𝔪, a • v = 0) →
          ∃ k : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), v = k 0 • c 0 + k 1 • c 1) →
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ a : Fin 2 → Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)),
          (∀ j : Fin 2, rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c j) =
            a j 0 • c 0 + a j 1 • c 1) ∧
          (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ p * 2 → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
              A'.IsFrobeniusAt σ ℓ → a 0 0 * a 1 1 - a 1 0 * a 0 1 = (ℓ : ↥(rationalHeckeAlgebra 2 (JZero p))))) →
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ i : Fin 2,
          rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c i) = c i) →
      False := by
  intro hfdA hcomm hmul 𝔪 h𝔪 c INDEP TORS SPAN STABFROB FIX
  letI := heckeModuleBar p
  letI : CommRing ↥(rationalHeckeAlgebra 2 (JZero p)) :=
    { (inferInstance : Ring ↥(rationalHeckeAlgebra 2 (JZero p))) with mul_comm := hmul }
  letI := moduleES p
  haveI := hfdA

  obtain ⟨K, instF, instAK, instFD, instSep, θ, hθ, hker⟩ :=
    exists_residueField_of_isMaximal_of_finiteDimensional ℚ_[2] ↥(rationalHeckeAlgebra 2 (JZero p)) 𝔪 h𝔪
  letI := instF; letI := instAK; haveI := instFD; haveI := instSep

  obtain ⟨O, iO1, iO2, iO3, iO4, iO5, iO6, iO7, iO8, iO9, htower, -, h2O⟩ :=
    PadicInt.exists_completeDVR_finiteResidueField_isFractionRing_of_finiteDimensional 2 K
  letI := iO1; letI := iO2; letI := iO3; letI := iO4; letI := iO5; letI := iO6; letI := iO7; letI := iO8; letI := iO9
  letI : Algebra ℤ_[2] K := ((algebraMap O K).comp (algebraMap ℤ_[2] O)).toAlgebra
  haveI : IsScalarTower ℤ_[2] O K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ_[2] ℚ_[2] K := IsScalarTower.of_algebraMap_eq fun z => by
    show (algebraMap O K) (algebraMap ℤ_[2] O z) = algebraMap ℚ_[2] K (algebraMap ℤ_[2] ℚ_[2] z)
    rw [htower z, PadicInt.algebraMap_apply]

  have TORSθ : ∀ a : ↥(rationalHeckeAlgebra 2 (JZero p)), θ a = 0 → ∀ i, a • c i = 0 :=
    fun a ha => TORS a ((hker a).mp ha)
  have INDEPθ : ∀ a : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), a 0 • c 0 + a 1 • c 1 = 0 → θ (a 0) = 0 ∧ θ (a 1) = 0 :=
    fun a ha => ⟨(hker _).mpr (INDEP a ha).1, (hker _).mpr (INDEP a ha).2⟩

  let j := jmap p K θ c hθ
  have hj : Function.Injective j := jmap_injective p K θ c hθ TORSθ INDEPθ

  have hgal : ∀ σ : G, ∃ g : (Fin 2 → K) →ₗ[K] (Fin 2 → K),
      rationalGaloisRep 2 (JZero p) G σ ∘ₗ j = j ∘ₗ g.restrictScalars ℚ_[2] ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ p * 2 → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        A'.IsFrobeniusAt σ ℓ → LinearMap.det g = (ℓ : K)) := by
    intro σ
    obtain ⟨M, hM, hfrob⟩ := STABFROB σ
    let N : Matrix (Fin 2) (Fin 2) K := fun i j' => θ (M j' i)
    refine ⟨Matrix.toLin' N, ?_, ?_⟩
    · refine LinearMap.ext fun u => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, toLin'_apply_eq]
      exact jmap_galois p K θ c hθ TORSθ (rationalGaloisRep 2 (JZero p) G σ) (hcomm σ) M hM u
    · intro ℓ hℓ hdvd A' hA' hfr
      rw [det_toLin'_fin_two]
      show θ (M 0 0) * θ (M 1 1) - θ (M 1 0) * θ (M 0 1) = ℓ
      rw [← map_mul, ← map_mul, ← map_sub, hfrob ℓ hℓ hdvd A' hA' hfr, map_natCast]
  choose g hg hgdet using hgal

  refine false_of_inertia_trivial_on_plane p B hB O K h2O (Wplane p O K j) (finrank_Wplane p O K j hj)
    (fun σ w hw => ((Wplane_stable p O K j σ (g σ) (hg σ)) w hw).1) ?_ ?_
  ·
    intro ℓ hℓ hℓp hℓ2 B' hB' σ hfr
    have hℓ2' : ℓ ≠ 2 := by simpa using hℓ2
    have hdvd : ¬ ℓ ∣ p * 2 := fun h => by
      rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h1
      · exact hℓp h1
      · exact hℓ2' ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
    obtain ⟨Ψ, hΨ⟩ := exists_conj_Wplane p O K j hj σ (g σ) (hg σ)
    have hR : ((rhoMES p O σ).baseChange K).restrict
          (fun w hw => ((Wplane_stable p O K j σ (g σ) (hg σ)) w hw).1) =
        (Ψ : (Fin 2 → K) →ₗ[K] ↥(Wplane p O K j)) ∘ₗ g σ ∘ₗ (Ψ.symm : ↥(Wplane p O K j) →ₗ[K] (Fin 2 → K)) := by
      refine LinearMap.ext fun w => ?_
      obtain ⟨u, rfl⟩ := Ψ.surjective w
      apply Subtype.ext
      simp only [LinearMap.coe_restrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hΨ u
    exact (congrArg (@LinearMap.det (↥(Wplane p O K j)) _ K _ _) hR).trans
      ((LinearMap.det_conj (M := Fin 2 → K) (N := ↥(Wplane p O K j)) (g σ) Ψ).trans (hgdet σ ℓ hℓ hdvd B' hB' hfr))
  ·
    intro σ hσ w hw

    let M1 : Fin 2 → Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)) := fun j' i => if i = j' then 1 else 0
    have hM : ∀ j' : Fin 2, rationalGaloisRep 2 (JZero p) G σ (c j') = M1 j' 0 • c 0 + M1 j' 1 • c 1 := by
      intro j'
      fin_cases j'
      · exact (FIX σ hσ 0).trans (by simp [M1])
      · exact (FIX σ hσ 1).trans (by simp [M1])
    have hid : rationalGaloisRep 2 (JZero p) G σ ∘ₗ j = j ∘ₗ (LinearMap.id : (Fin 2 → K) →ₗ[K] (Fin 2 → K)).restrictScalars ℚ_[2] := by
      refine LinearMap.ext fun u => ?_
      show rationalGaloisRep 2 (JZero p) G σ (j u) = j u
      refine (jmap_galois p K θ c hθ TORSθ (rationalGaloisRep 2 (JZero p) G σ) (hcomm σ) M1 hM u).trans ?_
      show j _ = j u
      congr 1
      funext i
      fin_cases i <;> simp [M1, Fin.sum_univ_two]
    obtain ⟨e, he, rfl⟩ := (mem_Wplane_iff p O K j).mp hw
    rw [((Wplane_stable p O K j σ LinearMap.id hid) _ hw).2 e he rfl]
    simp

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

end ModularCurve.NonTriv
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

end
p2m_reactivate "P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane.ModularCurve.NonTriv"

theorem solution (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∀ (hfdA : FiniteDimensional ℚ_[2] ↥(rationalHeckeAlgebra 2 (JZero p)))
      (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ↥(rationalHeckeAlgebra 2 (JZero p)))
        (v : RationalTateModule 2 (JZero p)),
        rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (a • v) =
          a • rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
      (hmul : ∀ a b : ↥(rationalHeckeAlgebra 2 (JZero p)), a * b = b * a)
      (𝔪 : Ideal ↥(rationalHeckeAlgebra 2 (JZero p))), 𝔪.IsMaximal →
    ∀ (c : Fin 2 → RationalTateModule 2 (JZero p)),
      (∀ a : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), a 0 • c 0 + a 1 • c 1 = 0 → a 0 ∈ 𝔪 ∧ a 1 ∈ 𝔪) →
      (∀ a ∈ 𝔪, ∀ i : Fin 2, a • c i = 0) →
      (∀ v : RationalTateModule 2 (JZero p), (∀ a ∈ 𝔪, a • v = 0) →
          ∃ k : Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)), v = k 0 • c 0 + k 1 • c 1) →
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ a : Fin 2 → Fin 2 → ↥(rationalHeckeAlgebra 2 (JZero p)),
          (∀ j : Fin 2, rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c j) =
            a j 0 • c 0 + a j 1 • c 1) ∧
          (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ p * 2 → ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
              A'.IsFrobeniusAt σ ℓ → a 0 0 * a 1 1 - a 1 0 * a 0 1 = (ℓ : ↥(rationalHeckeAlgebra 2 (JZero p))))) →
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ i : Fin 2,
          rationalGaloisRep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (c i) = c i) →
      False :=
  ModularCurve.NonTriv.l5_main p B hB

end S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane
end P2MW
export P2MW.S_ModularCurve_rationalTateModule_false_of_inertia_fixed_eigenplane (solution)
