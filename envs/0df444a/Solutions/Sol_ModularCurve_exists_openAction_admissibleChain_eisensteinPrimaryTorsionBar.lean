-- Prove2me | solution 1 for ModularCurve.exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c9eca759-f30a-505e-82af-bc58d7db9162

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_MazurAdmissible_GaloisModule
import Theorems.Thm_ModularCurve_eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_MazurAdmissible_AdmissibleChain_exists_map_addEquiv
import Theorems.Thm_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar
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

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar.ModularCurve MazurAdmissible P2MW.S_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar.MazurAdmissible"

namespace MazurAdmissible
p2m_export "MazurAdmissible" "OpenAction AdmissibleChain AdmissibleChain.exists_map_addEquiv AdmissibleChain.nonempty_of_addSubgroup"
p2m_open "MazurAdmissible"

variable {M : Type*} [AddCommGroup M]

namespace OpenAction p2m_export "MazurAdmissible.OpenAction" "φ hker" end OpenAction
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private noncomputable def _root_.MazurAdmissible.OpenAction.restrict' (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, Φ.φ σ x ∈ K) :
    OpenAction ↥K where
  φ :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨Φ.φ σ (x : M), hK σ (x : M) x.2⟩
          invFun := fun x => ⟨Φ.φ σ⁻¹ (x : M), hK σ⁻¹ (x : M) x.2⟩
          left_inv := fun x => by
            ext
            change (Φ.φ σ⁻¹) ((Φ.φ σ) (x : M)) = x
            rw [← AddAut.mul_apply', ← map_mul, inv_mul_cancel, map_one, AddAut.one_apply']
          right_inv := fun x => by
            ext
            change (Φ.φ σ) ((Φ.φ σ⁻¹) (x : M)) = x
            rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']
          map_add' := fun x y => by ext; exact map_add (Φ.φ σ) (x : M) (y : M) }
      map_one' := by
        ext x
        change Φ.φ 1 (x : M) = x
        rw [map_one]; rfl
      map_mul' := fun σ τ => by
        ext x
        change Φ.φ (σ * τ) (x : M) = Φ.φ σ (Φ.φ τ (x : M))
        rw [map_mul]; rfl }
  hker := by
    apply Subgroup.isOpen_mono _ Φ.hker
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext x
    change Φ.φ σ (x : M) = x
    rw [hσ]; rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.restrict'"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private noncomputable def _root_.MazurAdmissible.OpenAction.congr' {M' : Type*} [AddCommGroup M'] (Φ : OpenAction M)
    (e : M ≃+ M') : OpenAction M' where
  φ :=
    { toFun := fun σ => (e.symm.trans (Φ.φ σ)).trans e
      map_one' := by ext x; simp
      map_mul' := fun σ τ => by ext x; simp [AddAut.mul_apply'] }
  hker := by
    apply Subgroup.isOpen_mono _ Φ.hker
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext x
    simp [hσ]

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.congr'"
p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.congr'_apply {M' : Type*} [AddCommGroup M'] (Φ : OpenAction M)
    (e : M ≃+ M') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : M') :
    (Φ.congr' e).φ σ y = e (Φ.φ σ (e.symm y)) := rfl

end MazurAdmissible

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinPrimaryTorsionBar HeckeOperatorsCommuteBar heckeModuleBar modularFunctionFieldBar JZero HeckeAlg eisensteinMaximalIdeal eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar jZeroTorsionFinite"
namespace ADM5
p2m_open "ModularCurve"

theorem finite_carrier (p : ℕ) [Fact p.Prime] (q : ℕ) (hq : q.Prime) (m : ℕ) :
    Finite ↥(eisensteinPrimaryTorsionBar p q m) := by
  have hqm : 0 < q ^ m := pow_pos hq.pos m
  have hfinT : Finite ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (modularFunctionFieldBar p) (q ^ m)) := jZeroTorsionFinite p (q ^ m) hqm
  have hmem : ∀ x : ↥(eisensteinPrimaryTorsionBar p q m),
      ((x : JZero p) : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) ∈
        AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (q ^ m) := by
    intro x
    have hx : (((q : ℤ) ^ m) • AddMonoidHom.id (JZero p)) (x : JZero p) = 0 := x.2.1
    change ((q : ℤ) ^ m) • (x : JZero p) = 0 at hx
    refine (AlgebraicCurve.Pic0.mem_torsion (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar p)).mpr ?_
    push_cast
    exact hx
  refine Finite.of_injective
    (fun x => (⟨(x : JZero p), hmem x⟩ :
      ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (q ^ m))))
    (fun x y h => ?_)
  apply Subtype.ext
  simpa using congrArg Subtype.val h

theorem exists_le_torsionBySet_pow (p : ℕ) [Fact p.Prime] (q : ℕ) (hq : q.Prime) (m : ℕ) :
    letI := heckeModuleBar p
    ∃ k, eisensteinPrimaryTorsionBar p q m ≤
      (Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup := by
  classical
  letI := heckeModuleBar p
  have hTmono : Monotone (fun k : ℕ => (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup) := by
    intro k l hkl x hx
    have hsub : (↑((eisensteinMaximalIdeal p q) ^ l) : Set HeckeAlg) ⊆
        ↑((eisensteinMaximalIdeal p q) ^ k) :=
      SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right hkl)
    simp only [Submodule.mem_toAddSubgroup] at hx ⊢
    exact Submodule.torsionBySet_le_torsionBySet_of_subset hsub hx
  haveI := finite_carrier p q hq m
  have hx : ∀ x : ↥(eisensteinPrimaryTorsionBar p q m), ∃ k, (x : JZero p) ∈
      (fun k : ℕ => (Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup) k := by
    intro x
    exact (AddSubgroup.mem_iSup_of_directed hTmono.directed_le).mp x.2.2
  choose kx hkx using hx
  obtain ⟨K, hK⟩ := Finite.exists_le kx
  exact ⟨K, fun x hx' => hTmono (hK ⟨x, hx'⟩) (hkx ⟨x, hx'⟩)⟩

end ModularCurve.ADM5

set_option maxHeartbeats 3200000 in
theorem solution (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) (hq : q.Prime) (m : ℕ) :
    ∃ Φ : OpenAction ↥(eisensteinPrimaryTorsionBar p q m),
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(eisensteinPrimaryTorsionBar p q m)),
          (Φ.φ σ x : JZero p) = σ • (x : JZero p)) ∧
        Nonempty (AdmissibleChain q Φ) := by
  classical
  letI := heckeModuleBar p
  obtain ⟨k, hk⟩ := ModularCurve.ADM5.exists_le_torsionBySet_pow p q hq m

  obtain ⟨Φk, hΦk, ⟨ck⟩⟩ := eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar p hcomm q hq k

  obtain ⟨ι, hι⟩ : ∃ ι : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)) →+ JZero p, ∀ z, ι z = (z : JZero p) :=
    ⟨(Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).subtype.toAddMonoidHom, fun _ => rfl⟩
  let N := (eisensteinPrimaryTorsionBar p q m).comap ι
  have hmemN_iff : ∀ z, z ∈ N ↔ (z : JZero p) ∈ eisensteinPrimaryTorsionBar p q m := by
    intro z
    rw [AddSubgroup.mem_comap, hι]
  have hNstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ N, Φk.φ σ x ∈ N := by
    intro σ x hx
    rw [hmemN_iff] at hx ⊢
    rw [hΦk σ x]
    refine ⟨?_, ?_⟩
    · have h1 : (((q : ℤ) ^ m) • AddMonoidHom.id (JZero p)) (x : JZero p) = 0 := hx.1
      change ((q : ℤ) ^ m) • (x : JZero p) = 0 at h1
      show (((q : ℤ) ^ m) • AddMonoidHom.id (JZero p)) (σ • (x : JZero p)) = 0
      change ((q : ℤ) ^ m) • (σ • (x : JZero p)) = 0
      have h2 : σ • (((q : ℤ) ^ m) • (x : JZero p)) = ((q : ℤ) ^ m) • (σ • (x : JZero p)) :=
        map_zsmul (DistribSMul.toAddMonoidHom (JZero p) σ) ((q : ℤ) ^ m) (x : JZero p)
      rw [← h2, h1]
      exact map_zero (DistribSMul.toAddMonoidHom (JZero p) σ)
    · rw [← hΦk σ x]
      exact AddSubgroup.mem_iSup_of_mem k
        (by simpa only [Submodule.mem_toAddSubgroup] using (Φk.φ σ x).2)

  obtain ⟨ΦN, hΦN⟩ : ∃ ΦN : OpenAction ↥N, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (z : ↥N), ((ΦN.φ σ z : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg))) = Φk.φ σ z :=
    ⟨Φk.restrict' N hNstab, fun _ _ => rfl⟩
  obtain ⟨cN⟩ := AdmissibleChain.nonempty_of_addSubgroup hq Φk N hNstab ΦN hΦN ck

  have hinj : Function.Injective ι := by
    intro a b h
    rw [hι, hι] at h
    exact Subtype.ext h
  have hrange : eisensteinPrimaryTorsionBar p q m ≤ ι.range := by
    intro y hy
    exact ⟨⟨y, by simpa only [Submodule.mem_toAddSubgroup] using hk hy⟩, hι _⟩
  have hmap : N.map ι = eisensteinPrimaryTorsionBar p q m := AddSubgroup.map_comap_eq_self hrange
  obtain ⟨e, he⟩ : ∃ e : ↥N ≃+ ↥(eisensteinPrimaryTorsionBar p q m),
      ∀ z : ↥N, ((e z : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) = ι (z : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg))) :=
    ⟨(AddSubgroup.equivMapOfInjective N ι hinj).trans (AddEquiv.addSubgroupCongr hmap),
      fun z => by first | rfl | simp [AddSubgroup.coe_equivMapOfInjective_apply]⟩
  have hesymm : ∀ y : ↥(eisensteinPrimaryTorsionBar p q m),
      (((e.symm y : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg))) : JZero p) = (y : JZero p) := by
    intro y
    have h1 := he (e.symm y)
    rw [AddEquiv.apply_symm_apply, hι] at h1
    exact h1.symm
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : OpenAction ↥(eisensteinPrimaryTorsionBar p q m),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ↥(eisensteinPrimaryTorsionBar p q m)),
        Φ'.φ σ y = e (ΦN.φ σ (e.symm y)) :=
    ⟨ΦN.congr' e, fun σ y => OpenAction.congr'_apply ΦN e σ y⟩
  have hcompat : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N),
      Φ'.φ σ (e x) = e (ΦN.φ σ x) := fun σ x =>
    (hΦ' σ (e x)).trans (congrArg (fun w => e (ΦN.φ σ w)) (e.symm_apply_apply x))
  obtain ⟨c', -, -⟩ := AdmissibleChain.exists_map_addEquiv (Φ := ΦN) (Φ' := Φ') e hcompat cN
  refine ⟨Φ', fun σ y => ?_, ⟨c'⟩⟩
  calc ((Φ'.φ σ y : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = ((e (ΦN.φ σ (e.symm y)) : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) :=
        congrArg Subtype.val (hΦ' σ y)
    _ = ι ((ΦN.φ σ (e.symm y) : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg))) := he _
    _ = ι (Φk.φ σ ((e.symm y : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)))) := congrArg ι (hΦN σ _)
    _ = ((Φk.φ σ ((e.symm y : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)))) : JZero p) := hι _
    _ = σ • (((e.symm y : ↥N) : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg))) : JZero p) := hΦk σ _
    _ = σ • (y : JZero p) := by rw [hesymm]

end S_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar
end P2MW
export P2MW.S_ModularCurve_exists_openAction_admissibleChain_eisensteinPrimaryTorsionBar (solution)
