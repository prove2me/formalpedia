-- Prove2me | solution 1 for ModularCurve.nonempty_jZeroNeronPrimaryTorsionFlag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/67ff5f96-5db5-5097-86c2-6f52925ae66a

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Theorems.Thm_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag
import Theorems.Thm_HopfAlgebra_exists_constant_and_rootsOfUnity_models_of_rank
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFlag
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 800000

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
open CategoryTheory MazurAdmissible GaloisRep Opposite

theorem solution (p : ℕ) [Fact p.Prime]
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ) :
    Nonempty (JZeroNeronPrimaryTorsionFlag p q A hA C m) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : 0 < q := hq.pos
  letI := heckeModuleBar p

  obtain ⟨Φ, hΦ, ⟨chain⟩⟩ :=
    exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar p (heckeOperatorsCommuteBar p)
      q hq m
  let eTB := eisensteinPrimaryTorsionBar p q m
  let ιM : ↥eTB →+ JZero p := eTB.subtype
  have hιM_inj : Function.Injective ιM := Subtype.val_injective

  have hcardStep : ∀ i : Fin (chain.n + 1), Nat.card ↥(chain.step i) = q ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        rw [chain.hbot, Fin.val_zero, pow_zero]
        exact Nat.card_unique
    | succ i ih =>
        have hle := chain.hmono i
        have hLag : Nat.card ↥(chain.step i.succ)
            = Nat.card (↥(chain.step i.succ) ⧸
                (chain.step i.castSucc).addSubgroupOf (chain.step i.succ))
              * Nat.card ↥((chain.step i.castSucc).addSubgroupOf (chain.step i.succ)) :=
          AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
        have hsub : Nat.card ↥((chain.step i.castSucc).addSubgroupOf (chain.step i.succ))
            = Nat.card ↥(chain.step i.castSucc) :=
          Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
        rw [hLag, chain.hcard i, hsub, ih, Fin.coe_castSucc, Fin.val_succ, pow_succ, mul_comm]

  have hcardM : Nat.card ↥eTB = q ^ chain.n := by
    have h := hcardStep (Fin.last chain.n)
    rwa [chain.htop, Fin.val_last, Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h
  haveI hFinM : Finite ↥eTB := Nat.finite_of_card_ne_zero (hcardM ▸ pow_ne_zero _ hq0.ne')

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ q := by
    have hdeg : (Polynomial.cyclotomic q (AlgebraicClosure ℚ)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
  have hσζ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ a : ℕ, σ ζ = ζ ^ a := by
    intro σ
    have hpow : (σ ζ) ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, _, ha⟩ := hζ.eq_pow_of_pow_eq_one hpow
    exact ⟨a, ha.symm⟩
  have hstepStab : ∀ (i : Fin (chain.n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x : ↥eTB), x ∈ chain.step i → Φ.φ σ x ∈ chain.step i := by
    intro i
    induction i using Fin.induction with
    | zero =>
        intro σ x hx
        rw [chain.hbot, AddSubgroup.mem_bot] at hx
        rw [chain.hbot, AddSubgroup.mem_bot, hx, map_zero]
    | succ i ih =>
        intro σ x hx
        have hle := chain.hmono i
        have hact := chain.hact i
        rcases htag : chain.tag i with _ | _
        ·
          simp only [htag, Bool.false_eq_true, if_false] at hact
          obtain ⟨a, ha⟩ := hσζ σ
          have h1 : Φ.φ σ x - a • x ∈ chain.step i.castSucc := hact σ ζ hζ a ha x hx
          have : Φ.φ σ x = (Φ.φ σ x - a • x) + a • x := (sub_add_cancel _ _).symm
          rw [this]
          exact (chain.step i.succ).add_mem (hle h1) ((chain.step i.succ).nsmul_mem hx a)
        ·
          simp only [htag, if_true] at hact
          have h1 : Φ.φ σ x - x ∈ chain.step i.castSucc := hact σ x hx
          have : Φ.φ σ x = (Φ.φ σ x - x) + x := (sub_add_cancel _ _).symm
          rw [this]; exact (chain.step i.succ).add_mem (hle h1) hx

  let act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ↥eTB → ↥eTB := fun σ x ↦ Φ.φ σ x
  have hact_genericGalois : ∀ σ (f g : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)),
      (∀ h, g h = σ (f h)) → C.genericPoints m g = act σ (C.genericPoints m f) := by
    intro σ f g hfg
    apply Subtype.ext
    rw [C.genericGalois m σ f g hfg]
    exact (hΦ σ (C.genericPoints m f)).symm

  have hRℤ : Function.Injective (algebraMap ℤ (AlgebraicClosure ℚ)) :=
    (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int
  have hflat_SH : @Module.Flat ℤ (C.H m) _ _
      (@Algebra.toModule ℤ (C.H m) _ _ (C.instHopfAlgebra_H m).toAlgebra) := by
    convert C.instFlat_H m using 1
    all_goals first | rfl | exact Subsingleton.elim _ _
  obtain ⟨B, iCR_B, iHA_B, πZ, φZ, hFT_B, hFlat_B, hπsurj, hφsurj, hφπ, hπlast, hfactors,
          hcocomm_of, hfin_of⟩ :=
    @HopfAlgebra.exists_quotientFlag_of_galoisStableChain ℤ _ _ _ _ hRℤ (C.H m)
      _ (C.instHopfAlgebra_H m) _ hflat_SH
      ↥eTB _ _ (C.genericPoints m) (C.genericConv m) act hact_genericGalois
      chain.n chain.step chain.hmono chain.htop hstepStab
  letI : ∀ i, CommRing (B i) := iCR_B
  letI : ∀ i, HopfAlgebra ℤ (B i) := iHA_B
  haveI : ∀ i, Algebra.FiniteType ℤ (B i) := hFT_B
  haveI : ∀ i, Module.Flat ℤ (B i) := fun i ↦ by
    convert hFlat_B i using 1
    all_goals first | rfl | exact Subsingleton.elim _ _

  obtain ⟨F, ιF, incl, FE, hMono, hincl_ι, hIsIso_last, hCompat⟩ :=
    AlgebraicGeometry.Scheme.exists_fppfSubsheafFlag_of_bialgHomFlag specInt (C.𝒥 m) (C.H m)
      (C.sectionsEquiv m) (C.sectionsNat m)
      chain.n B πZ hπsurj φZ hφπ hπlast

  let kind : Fin chain.n → JZeroFlagLayerKind :=
    fun i ↦ if chain.tag i then .const else .mult
  have hLff : ∀ (i : Fin chain.n) (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓp : ℓ ≠ p),
      ∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra (ratLocalizedAt ℓ) K),
        Module.Finite (ratLocalizedAt ℓ) K ∧ Module.Flat (ratLocalizedAt ℓ) K ∧
        Module.finrank (ratLocalizedAt ℓ) K = q ∧
        Nat.card (K →ₐ[ratLocalizedAt ℓ] AlgebraicClosure ℚ) = q ∧
        (kind i = .const →
          Nonempty (K ≃ₐ[ratLocalizedAt ℓ] (Fin q → ratLocalizedAt ℓ))) ∧
        (kind i = .mult →
          Nonempty (K ≃ₐ[ratLocalizedAt ℓ]
            (Polynomial (ratLocalizedAt ℓ) ⧸
              Ideal.span {(Polynomial.X : Polynomial (ratLocalizedAt ℓ)) ^ q - 1}))) := by
    intro i ℓ hℓ _hℓp
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hmodels := HopfAlgebra.exists_constant_and_rootsOfUnity_models_of_rank
      (ratLocalizedAt ℓ) q (AlgebraicClosure ℚ)
    rcases hkind : kind i with _ | _
    · obtain ⟨K, iCR, iHA, hFin, hFlat, hrank, hcard, hiso⟩ := hmodels.1
      exact ⟨K, iCR, iHA, hFin, hFlat, hrank, hcard, fun _ ↦ hiso,
        fun h ↦ JZeroFlagLayerKind.noConfusion h⟩
    · obtain ⟨K, iCR, iHA, hFin, hFlat, hrank, hcard, hiso⟩ := hmodels.2
      exact ⟨K, iCR, iHA, hFin, hFlat, hrank, hcard,
        fun h ↦ JZeroFlagLayerKind.noConfusion h, fun _ ↦ hiso⟩
  choose Lff' iCR_Lff iHA_Lff hFin_Lff hFlat_Lff hrank_Lff hcard_Lff hisoConst hisoMult using hLff

  let gStep : Fin (chain.n + 1) → AddSubgroup (JZero p) := fun i ↦ (chain.step i).map ιM
  have hgStep_card : ∀ i, Nat.card ↥(gStep i) = q ^ (i : ℕ) := fun i ↦ by
    rw [show gStep i = (chain.step i).map ιM from rfl,
      Nat.card_congr (AddSubgroup.equivMapOfInjective _ ιM hιM_inj).toEquiv.symm]
    exact hcardStep i
  have hstep_mono : Monotone chain.step := fun i j hij ↦ by
    induction j using Fin.induction with
    | zero => exact Fin.le_zero_iff.mp hij ▸ le_rfl
    | succ j ih =>
      rcases eq_or_lt_of_le hij with heq | hlt
      · exact heq ▸ le_rfl
      · have hij' : i ≤ j.castSucc := by
          have := Fin.lt_def.mp hlt
          simp only [Fin.val_succ] at this
          exact Fin.le_def.mpr (by simp only [Fin.coe_castSucc]; omega)
        exact (ih hij').trans (chain.hmono j)
  have hgStep_mono : Monotone gStep := fun i j hij ↦ AddSubgroup.map_mono (hstep_mono hij)
  have hgStep_layer_card : ∀ i : Fin chain.n,
      Nat.card (↥(gStep i.succ) ⧸ (gStep i.castSucc).addSubgroupOf (gStep i.succ)) = q := by
    intro i
    have hle : gStep i.castSucc ≤ gStep i.succ := hgStep_mono (Fin.castSucc_le_succ i)
    have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      ((gStep i.castSucc).addSubgroupOf (gStep i.succ))
    rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv,
      hgStep_card i.succ, hgStep_card i.castSucc, Fin.val_succ, Fin.coe_castSucc, pow_succ] at hLag
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 _) (hLag.symm.trans (mul_comm _ _))

  letI : ∀ i ℓ hℓ hℓp, CommRing (Lff' i ℓ hℓ hℓp) := iCR_Lff
  letI : ∀ i ℓ hℓ hℓp, HopfAlgebra (ratLocalizedAt ℓ) (Lff' i ℓ hℓ hℓp) := iHA_Lff
  refine ⟨{
    n := chain.n
    G := B
    π := fun i ↦ (πZ i : C.H m →ₐ[ℤ] B i)
    π_surj := hπsurj
    quot := fun i ↦ (φZ i : B i.succ →ₐ[ℤ] B i.castSucc)
    quot_surj := hφsurj
    quot_π := fun i ↦ by
      ext h; exact DFunLike.congr_fun (congrArg BialgHom.toAlgHom (hφπ i)) h
    F := F
    ι := ιF
    ι_mono := hMono
    incl := incl
    incl_ι := hincl_ι
    F_sectionsEquiv := FE
    F_sectionsCompat := hCompat
    G_zero_subsingleton := ⟨fun g g' ↦ ?Gzero⟩
    isIso_ι_last := hIsIso_last
    genericStep := gStep
    genericStep_le_tors := fun i ↦ AddSubgroup.map_subtype_le _
    genericStep_mono := hgStep_mono
    genericStep_bot := by simp only [gStep, chain.hbot, AddSubgroup.map_bot]
    genericStep_top := by
      show (chain.step (Fin.last chain.n)).map ιM = eTB
      rw [chain.htop]
      simp only [ιM, ← AddMonoidHom.range_eq_map, AddSubgroup.range_subtype]
    genericStep_galois := ?gGalois
    genericStep_pin := ?gPin
    kind := kind
    layerAction_const := ?layConst
    layerAction_mult := ?layMult
    Lff := Lff'
    Lff_rank := hrank_Lff
    Lff_points := ?LffPts
    layerIsoConst := fun i hi ℓ hℓ hℓp ↦ hisoConst i ℓ hℓ hℓp hi
    layerIsoMult := fun i hi ℓ hℓ hℓp ↦ hisoMult i ℓ hℓ hℓp hi
    instFinite_Lff := hFin_Lff
    instFlat_Lff := hFlat_Lff
  }⟩

  case Gzero =>
    have hf : ∀ (g : B 0 →ₐ[ℤ] AlgebraicClosure ℚ),
        C.genericPoints m (WithConv.toConv (g.comp (πZ 0 : C.H m →ₐ[ℤ] B 0))) = 0 := by
      intro g
      have := (hfactors 0 (g.comp (πZ 0 : _ →ₐ[ℤ] _))).mp ⟨g, rfl⟩
      rw [chain.hbot] at this; simpa using this
    have heq0 : C.genericPoints m (WithConv.toConv (g.comp (πZ 0 : _ →ₐ[ℤ] _)))
        = C.genericPoints m (WithConv.toConv (g'.comp (πZ 0 : _ →ₐ[ℤ] _))) := by
      rw [hf g, hf g']
    have hcomp : (g.comp (πZ 0 : _ →ₐ[ℤ] _) : C.H m →ₐ[ℤ] _)
        = (g'.comp (πZ 0 : _ →ₐ[ℤ] _) : C.H m →ₐ[ℤ] _) := by
      have h := congrArg WithConv.ofConv ((C.genericPoints m).injective heq0)
      simpa only [WithConv.ofConv_toConv] using h
    exact AlgHom.ext fun b ↦ by
      obtain ⟨h, rfl⟩ := hπsurj 0 b
      exact DFunLike.congr_fun hcomp h
  case gGalois =>
    rintro i σ x ⟨y, hy, rfl⟩
    refine ⟨Φ.φ σ y, hstepStab i σ y hy, ?_⟩
    simp only [ιM, AddSubgroup.coe_subtype]; exact hΦ σ y
  case gPin =>
    intro i x
    simp only [gStep, AddSubgroup.mem_map, AddSubgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : C.genericPoints m
          (WithConv.toConv (WithConv.ofConv ((C.genericPoints m).symm y))) ∈ chain.step i := by
        rw [WithConv.toConv_ofConv, Equiv.apply_symm_apply]; exact hy
      obtain ⟨g, hg⟩ := (hfactors i _).mpr hy'
      exact ⟨g, by rw [hg, WithConv.toConv_ofConv, Equiv.apply_symm_apply]; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, (hfactors i _).mp ⟨g, rfl⟩, rfl⟩
  case layConst =>
    rintro i hi σ x ⟨y, hy, rfl⟩
    have htag : chain.tag i = true := by
      simp only [kind] at hi; by_contra h; simp [h] at hi
    have hact := chain.hact i; rw [htag] at hact; simp only [if_true] at hact
    have h1 : Φ.φ σ y - y ∈ chain.step i.castSucc := hact σ y hy
    refine ⟨Φ.φ σ y - y, h1, ?_⟩
    simp only [ιM, AddSubgroup.coe_subtype, map_sub]
    rw [hΦ σ y]
  case layMult =>
    rintro i hi σ nσ hnσ x ⟨y, hy, rfl⟩
    have htag : chain.tag i = false := by
      simp only [kind] at hi; by_contra h; simp [h] at hi
    have hact := chain.hact i; rw [htag] at hact; simp only [Bool.false_eq_true, if_false] at hact
    have hnσζ : σ ζ = ζ ^ nσ := hnσ ζ hζ.pow_eq_one
    have h1 : Φ.φ σ y - nσ • y ∈ chain.step i.castSucc := hact σ ζ hζ nσ hnσζ y hy
    refine ⟨Φ.φ σ y - nσ • y, h1, ?_⟩
    simp only [ιM, AddSubgroup.coe_subtype, map_sub, map_nsmul]
    rw [hΦ σ y]
  case LffPts =>
    intro i ℓ hℓ hℓp
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hL : Nat.card (WithConv (Lff' i ℓ hℓ hℓp →ₐ[ratLocalizedAt ℓ] AlgebraicClosure ℚ)) = q := by
      rw [Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv,
        WithConv.toConv_ofConv, WithConv.ofConv_toConv⟩]
      exact hcard_Lff i ℓ hℓ hℓp
    have hR : Nat.card (↥(gStep i.succ) ⧸ (gStep i.castSucc).addSubgroupOf (gStep i.succ)) = q :=
      hgStep_layer_card i
    haveI : Finite (WithConv (Lff' i ℓ hℓ hℓp →ₐ[ratLocalizedAt ℓ] AlgebraicClosure ℚ)) :=
      Nat.finite_of_card_ne_zero (by rw [hL]; exact hq0.ne')
    haveI : Finite (↥(gStep i.succ) ⧸ (gStep i.castSucc).addSubgroupOf (gStep i.succ)) :=
      Nat.finite_of_card_ne_zero (by rw [hR]; exact hq0.ne')
    exact ((Finite.equivFin _).trans (finCongr hL)).trans
      (((Finite.equivFin _).trans (finCongr hR)).symm)

end S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFlag
end P2MW
export P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFlag (solution)
