-- Prove2me | solution 1 for ModularCurve.eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0513797c-a1b3-53c5-bd68-07d9e15affa0

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_MazurAdmissible_GaloisModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Theorems.Thm_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
import Theorems.Thm_Fin_exists_chain_append
import Theorems.Thm_ModularCurve_finite_torsionBySet_eisensteinMaximalIdeal_pow
import Theorems.Thm_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal
import Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve AlgebraicCurve MazurAdmissible

noncomputable section

namespace P2mWs11Glue

attribute [local instance] ModularCurve.heckeModuleBar

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] {q : ℕ}

abbrev T (p : ℕ) [Fact p.Prime] (q k : ℕ) : Submodule HeckeAlg (JZero p) :=
  Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)

theorem mem_T_iff {k : ℕ} {x : JZero p} :
    x ∈ T p q k ↔ ∀ t ∈ (eisensteinMaximalIdeal p q) ^ k, t • x = 0 := by
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t.1 t.2⟩

theorem T_mono {k l : ℕ} (hkl : k ≤ l) : T p q k ≤ T p q l :=
  Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_pow_right hkl)

theorem T_zero : T p q 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_T_iff] at hx
  have := hx 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
  rw [one_smul] at this
  rw [this]
  exact Submodule.zero_mem _

theorem smul_mem_T [SMulCommClass Gal HeckeAlg (JZero p)] {k : ℕ} (σ : Gal) {x : JZero p}
    (hx : x ∈ T p q k) : σ • x ∈ T p q k := by
  rw [mem_T_iff] at hx ⊢
  intro t ht
  calc t • σ • x = σ • t • x := (smul_comm σ t x).symm
    _ = σ • (0 : JZero p) := by rw [hx t ht]
    _ = 0 := smul_zero (A := JZero p) σ

theorem nsmul_mem_T {k : ℕ} {x : JZero p} (hx : x ∈ T p q (k + 1)) : q • x ∈ T p q k := by
  rw [mem_T_iff] at hx ⊢
  intro t ht
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg, ← mul_smul]
  apply hx
  rw [pow_succ]
  exact Ideal.mul_mem_mul ht (natCast_mem_eisensteinMaximalIdeal p q)

theorem smul_mem_T_one {k : ℕ} {x : JZero p} (hx : x ∈ T p q (k + 1)) {t : HeckeAlg}
    (ht : t ∈ (eisensteinMaximalIdeal p q) ^ k) :
    t • x ∈ Submodule.torsionBySet HeckeAlg (JZero p)
      (↑(eisensteinMaximalIdeal p q) : Set HeckeAlg) := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨s, hs⟩
  rw [mem_T_iff] at hx
  rw [← mul_smul]
  apply hx
  rw [pow_succ']
  exact Ideal.mul_mem_mul hs ht

theorem quad_mem_T [SMulCommClass Gal HeckeAlg (JZero p)] (hcomm : HeckeOperatorsCommuteBar p)
    (hq : q.Prime) {k : ℕ} (σ : Gal) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ q)
    (a : ℕ) (ha : σ ζ = ζ ^ a) {x : JZero p} (hx : x ∈ T p q (k + 1)) :
    σ • σ • x - (1 + a) • (σ • x) + a • x ∈ T p q k := by
  rw [mem_T_iff]
  intro t ht
  have h := ModularCurve.smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal
    p hcomm q hq σ ζ hζ a ha (t • x) (smul_mem_T_one hx ht)
  rw [smul_add, smul_sub, ← smul_comm σ t (σ • x), ← smul_comm σ t x, smul_comm t (1 + a) (σ • x),
    ← smul_comm σ t x, smul_comm t a x]
  exact h

section Action

variable (p q)
variable [SMulCommClass Gal HeckeAlg (JZero p)]

def galAut (k : ℕ) (σ : Gal) : ↥(T p q k) ≃+ ↥(T p q k) where
  toFun x := ⟨σ • (x : JZero p), smul_mem_T σ x.2⟩
  invFun x := ⟨σ⁻¹ • (x : JZero p), smul_mem_T σ⁻¹ x.2⟩
  left_inv x := Subtype.ext (inv_smul_smul σ (x : JZero p))
  right_inv x := Subtype.ext (smul_inv_smul σ (x : JZero p))
  map_add' x y := Subtype.ext (smul_add σ (x : JZero p) (y : JZero p))

def galHom (k : ℕ) : Gal →* AddAut ↥(T p q k) where
  toFun := galAut p q k
  map_one' := by
    apply AddEquiv.ext
    intro x
    apply Subtype.ext
    exact one_smul Gal (x : JZero p)
  map_mul' σ τ := by
    apply AddEquiv.ext
    intro x
    apply Subtype.ext
    exact mul_smul σ τ (x : JZero p)

theorem coe_galHom (k : ℕ) (σ : Gal) (x : ↥(T p q k)) :
    ((galHom p q k σ x : ↥(T p q k)) : JZero p) = σ • (x : JZero p) := rfl

theorem isOpen_ker_galHom (k : ℕ) [Finite ↥(T p q k)] :
    IsOpen ((galHom p q k).ker : Set Gal) := by
  have hker : ((galHom p q k).ker : Set Gal) =
      ⋂ x : ↥(T p q k), (MulAction.stabilizer Gal (x : JZero p) : Set Gal) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    constructor
    · intro h x
      have := AddEquiv.congr_fun h x
      exact congrArg Subtype.val this
    · intro h
      apply AddEquiv.ext
      intro x
      exact Subtype.ext (h x)
  rw [hker]
  exact isOpen_iInter_of_finite (fun x => ModularCurve.JZero.isOpen_stabilizer p (x : JZero p))

end Action

theorem nsmul_mem_of_card_quotient {M : Type*} [AddCommGroup M] {X Y : AddSubgroup M} {n : ℕ}
    (h : Nat.card (↥Y ⧸ X.addSubgroupOf Y) = n) {x : M} (hx : x ∈ Y) : n • x ∈ X := by
  have h1 : Nat.card (↥Y ⧸ X.addSubgroupOf Y) •
      (QuotientAddGroup.mk (⟨x, hx⟩ : ↥Y) : ↥Y ⧸ X.addSubgroupOf Y) = 0 :=
    card_nsmul_eq_zero'
  rw [h, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
  exact h1

theorem mod_eq_of_apply_eq_pow {q : ℕ} (hq : q.Prime) {ζ ζ' : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ q) (hζ' : IsPrimitiveRoot ζ' q) (σ : Gal) {a c : ℕ}
    (hc : σ ζ = ζ ^ c) (ha : σ ζ' = ζ' ^ a) : a % q = c % q := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hζ0 : ζ' ≠ 0 := hζ'.ne_zero hq.ne_zero
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hσζ' : σ (ζ ^ j) = (ζ ^ j) ^ c := by
    rw [map_pow, hc, ← pow_mul, ← pow_mul, mul_comm]
  have hdvd : (q : ℤ) ∣ (a : ℤ) - c := by
    rw [← hζ'.zpow_eq_one_iff_dvd, zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, ← ha, hσζ',
      div_self (pow_ne_zero _ hζ0)]
  exact (Nat.modEq_iff_dvd.mpr hdvd).symm

theorem sub_nsmul_mem {M : Type*} [AddCommGroup M] {X : AddSubgroup M} {y x : M} {a c n : ℕ}
    (hac : a % n = c % n) (hcx : y - c • x ∈ X) (hnx : n • x ∈ X) : y - a • x ∈ X := by
  have hsplit : ∀ b : ℕ, b • x = (b / n) • (n • x) + (b % n) • x := by
    intro b
    conv_lhs => rw [← Nat.div_add_mod' b n]
    rw [add_nsmul, smul_smul]
  have e : y - a • x = (y - c • x) + (c / n) • (n • x) - (a / n) • (n • x) := by
    rw [hsplit a, hsplit c, hac]
    abel
  rw [e]
  exact X.sub_mem (X.add_mem hcx (X.nsmul_mem hnx _)) (X.nsmul_mem hnx _)

section Filtration

variable (p q)
variable [SMulCommClass Gal HeckeAlg (JZero p)]

def Afil (m k : ℕ) : AddSubgroup ↥(T p q m) :=
  (T p q k).toAddSubgroup.comap (T p q m).toAddSubgroup.subtype

variable {p q}

theorem mem_Afil {m k : ℕ} (x : ↥(T p q m)) : x ∈ Afil p q m k ↔ (x : JZero p) ∈ T p q k :=
  Iff.rfl

theorem Afil_zero (m : ℕ) : Afil p q m 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_Afil, T_zero, Submodule.mem_bot] at hx
  rw [AddSubgroup.mem_bot]
  exact Subtype.ext hx

theorem Afil_self (m : ℕ) : Afil p q m m = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_Afil]
  exact x.2

theorem Afil_mono (m k : ℕ) : Afil p q m k ≤ Afil p q m (k + 1) := fun x hx =>
  (mem_Afil x).mpr (T_mono (Nat.le_succ k) ((mem_Afil x).mp hx))

theorem Afil_stab (m k : ℕ) (σ : Gal) (x : ↥(T p q m)) (hx : x ∈ Afil p q m k) :
    galHom p q m σ x ∈ Afil p q m k := by
  rw [mem_Afil] at hx ⊢
  exact smul_mem_T σ hx

theorem Afil_nsmul (m k : ℕ) (x : ↥(T p q m)) (hx : x ∈ Afil p q m (k + 1)) :
    q • x ∈ Afil p q m k := by
  rw [mem_Afil] at hx ⊢
  exact nsmul_mem_T hx

theorem Afil_quad (hcomm : HeckeOperatorsCommuteBar p) (hq : q.Prime) (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ q) (m k : ℕ) (σ : Gal) (c : ℕ) (hc : σ ζ = ζ ^ c)
    (x : ↥(T p q m)) (hx : x ∈ Afil p q m (k + 1)) :
    galHom p q m σ (galHom p q m σ x - c • x) - (galHom p q m σ x - c • x) ∈ Afil p q m k := by
  rw [mem_Afil] at hx ⊢
  have e : ((galHom p q m σ (galHom p q m σ x - c • x) - (galHom p q m σ x - c • x) : ↥(T p q m)) :
      JZero p) = σ • σ • (x : JZero p) - (1 + c) • (σ • (x : JZero p)) + c • (x : JZero p) := by
    simp only [Submodule.coe_sub, coe_galHom, Submodule.coe_smul_of_tower, smul_sub, add_smul,
      one_smul]
    rw [← smul_comm c σ (x : JZero p)]
    abel
  rw [e]
  exact quad_mem_T hcomm hq σ ζ hζ c hc hx

def StepRel (m : ℕ) (χ : Gal →* (ZMod q)ˣ) (X Y : AddSubgroup ↥(T p q m)) : Prop :=
  X ≤ Y ∧ Nat.card (↥Y ⧸ X.addSubgroupOf Y) = q ∧
    ((∀ g : Gal, ∀ x ∈ Y, galHom p q m g x - x ∈ X) ∨
     (∀ g : Gal, ∀ x ∈ Y, galHom p q m g x - (χ g : ZMod q).val • x ∈ X))

theorem exists_chain (hcomm : HeckeOperatorsCommuteBar p) (hq : q.Prime) (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ q) (m : ℕ) [Finite ↥(T p q m)] (χ : Gal →* (ZMod q)ˣ)
    (hχ : ∀ σ : Gal, σ ζ = ζ ^ (χ σ : ZMod q).val) (k : ℕ) :
    ∃ (n : ℕ) (step : Fin (n + 1) → AddSubgroup ↥(T p q m)),
      step 0 = Afil p q m 0 ∧ step (Fin.last n) = Afil p q m k ∧
        ∀ i : Fin n, StepRel m χ (step i.castSucc) (step i.succ) := by
  induction k with
  | zero => exact ⟨0, fun _ => Afil p q m 0, rfl, rfl, fun i => i.elim0⟩
  | succ k ih =>
    refine Fin.exists_chain_append (StepRel m χ) ih ?_
    exact AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
      (galHom p q m) hq χ (Afil p q m k) (Afil p q m (k + 1)) (Afil_mono m k) inferInstance
      (Afil_stab m k) (Afil_stab m (k + 1)) (Afil_nsmul m k)
      (fun σ x hx => Afil_quad hcomm hq ζ hζ m k σ _ (hχ σ) x hx)

def openAction (m : ℕ) [Finite ↥(T p q m)] : OpenAction ↥(T p q m) :=
  ⟨galHom p q m, isOpen_ker_galHom p q m⟩

theorem nonempty_admissibleChain (hq : q.Prime) (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ q) (m : ℕ) [Finite ↥(T p q m)] (χ : Gal →* (ZMod q)ˣ)
    (hχ : ∀ σ : Gal, σ ζ = ζ ^ (χ σ : ZMod q).val)
    (n : ℕ) (step : Fin (n + 1) → AddSubgroup ↥(T p q m))
    (h0 : step 0 = ⊥) (hlast : step (Fin.last n) = ⊤)
    (hS : ∀ i : Fin n, StepRel m χ (step i.castSucc) (step i.succ)) :
    Nonempty (AdmissibleChain q (openAction (p := p) (q := q) m)) := by
  classical
  refine ⟨{
    n := n
    step := step
    hbot := h0
    htop := hlast
    hmono := fun i => (hS i).1
    tag := fun i => decide (∀ g : Gal, ∀ x ∈ step i.succ, galHom p q m g x - x ∈ step i.castSucc)
    hcard := fun i => (hS i).2.1
    hact := ?_ }⟩
  intro i
  by_cases htriv : ∀ g : Gal, ∀ x ∈ step i.succ, galHom p q m g x - x ∈ step i.castSucc
  · rw [if_pos (decide_eq_true htriv)]
    exact htriv
  · rw [if_neg (by rw [decide_eq_false htriv]; exact Bool.false_ne_true)]
    have hcyc := (hS i).2.2.resolve_left htriv
    intro σ ζ' hζ' a ha x hx
    have hmod : a % q = (χ σ : ZMod q).val % q := mod_eq_of_apply_eq_pow hq hζ hζ' σ (hχ σ) ha
    have hqx : q • x ∈ step i.castSucc := nsmul_mem_of_card_quotient (hS i).2.1 hx
    change galHom p q m σ x - a • x ∈ step i.castSucc
    exact sub_nsmul_mem hmod (hcyc σ x hx) hqx

end Filtration

theorem main (hcomm : HeckeOperatorsCommuteBar p) (hq : q.Prime) (m : ℕ) :
    ∃ Φ : OpenAction ↥(T p q m),
      (∀ (σ : Gal) (x : ↥(T p q m)), (Φ.φ σ x : JZero p) = σ • (x : JZero p)) ∧
        Nonempty (AdmissibleChain q Φ) := by
  haveI : SMulCommClass Gal HeckeAlg (JZero p) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm
  haveI : Finite ↥(T p q m) :=
    ModularCurve.finite_torsionBySet_eisensteinMaximalIdeal_pow p q hq m
  haveI : NeZero q := ⟨hq.ne_zero⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ q := by
    haveI : NeZero ((q : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q (AlgebraicClosure ℚ))
      (by
        rw [Polynomial.degree_cyclotomic]
        exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne')
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
  let χ : Gal →* (ZMod q)ˣ := hζ.autToPow ℚ
  have hχ : ∀ σ : Gal, σ ζ = ζ ^ (χ σ : ZMod q).val := fun σ => (hζ.autToPow_spec ℚ σ).symm
  obtain ⟨n, step, h0, hlast, hS⟩ := exists_chain hcomm hq ζ hζ m χ hχ m
  rw [Afil_zero] at h0
  rw [Afil_self] at hlast
  exact ⟨openAction m, fun σ x => rfl, nonempty_admissibleChain hq ζ hζ m χ hχ n step h0 hlast hS⟩

end P2mWs11Glue

end

theorem solution (p : ℕ)
    [Fact p.Prime] (hcomm : ModularCurve.HeckeOperatorsCommuteBar p) (q : ℕ) (hq : q.Prime) :
    ∀ m : ℕ,
      letI := heckeModuleBar p
      ∃ Φ : OpenAction ↥(Submodule.torsionBySet HeckeAlg (JZero p)
          (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)),
        (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
            (x : ↥(Submodule.torsionBySet HeckeAlg (JZero p)
              (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg))),
            (Φ.φ σ x : JZero p) = σ • (x : JZero p)) ∧
          Nonempty (AdmissibleChain q Φ) :=
  fun m => P2mWs11Glue.main hcomm hq m

end S_ModularCurve_eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar
end P2MW
export P2MW.S_ModularCurve_eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar (solution)
