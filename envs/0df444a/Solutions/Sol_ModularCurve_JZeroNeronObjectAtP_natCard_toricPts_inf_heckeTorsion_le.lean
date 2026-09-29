-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.natCard_toricPts_inf_heckeTorsion_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/201abe41-9a31-5860-8a07-7b345ecc183b

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Theorems.Thm_ModularCurve_det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_natCard_toricPts_inf_heckeTorsion_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE TateModule.instModule TateModule.instSMul WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one"
p2m_attr_erase "simp" "AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply"
p2m_attr_erase "simp" "GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (hp2 : p ≠ 2) (hin : HeckeInputsAll (N₀ * p)) (hcomm : HeckeOperatorsCommuteBar (N₀ * p))
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪.IsMaximal) (hE : ¬ IsEventuallyEisenstein 𝔪) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hfin : Finite (HeckeAlg ⧸ 𝔪))
    (h2 : letI := heckeModuleBar (N₀ * p);
      Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero (N₀ * p)) 𝔪) = 2) :
    Nat.card ↥(O.toricPts p ⊓ (letI := heckeModuleBar (N₀ * p);
        (heckeTorsion (JZero (N₀ * p)) 𝔪).toAddSubgroup)) ≤ Nat.card (HeckeAlg ⧸ 𝔪) := by
  classical
  letI instNp : Module HeckeAlg (JZero (N₀ * p)) := heckeModuleBar (N₀ * p)
  haveI : 𝔪.IsMaximal := h𝔪
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Finite (HeckeAlg ⧸ 𝔪) := hfin
  haveI hsc : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero (N₀ * p)) :=
    smulCommClass_JZero_of_heckeOperatorsCommuteBar (N₀ * p) hcomm
  have hp : p.Prime := Fact.out
  set W : Submodule HeckeAlg (JZero (N₀ * p)) := heckeTorsion (JZero (N₀ * p)) 𝔪 with hW
  show Nat.card ↥(O.toricPts p ⊓ W.toAddSubgroup) ≤ Nat.card (HeckeAlg ⧸ 𝔪)
  haveI : Module.Finite (HeckeAlg ⧸ 𝔪) ↥W := Module.finite_of_finrank_eq_succ h2
  haveI : Finite ↥W := Module.finite_of_finite (HeckeAlg ⧸ 𝔪)

  set c : ℕ := ((-1 : (ZMod p)ˣ) : ZMod p).val with hc
  have key : ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ ∧
      ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ c :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hp hA (-1)
  obtain ⟨σ, hσI, hσ⟩ := key

  let ρ := mTorsionGaloisRep (JZero (N₀ * p)) 𝔪 σ
  let E : Submodule (HeckeAlg ⧸ 𝔪) ↥W := LinearMap.ker (ρ - (c : HeckeAlg ⧸ 𝔪) • LinearMap.id)
  have hmemE : ∀ w : ↥W, w ∈ E ↔ σ • (w : JZero (N₀ * p)) = c • (w : JZero (N₀ * p)) := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      simpa [ρ, mTorsionGaloisRep, Nat.cast_smul_eq_nsmul] using h'
    · intro h
      apply Subtype.ext
      simpa [ρ, mTorsionGaloisRep, Nat.cast_smul_eq_nsmul] using h

  have htoric : ∀ v ∈ O.toricPts p, σ • v = c • v := by
    intro v hv
    unfold toricPts at hv
    rw [dif_pos hp.pos] at hv
    refine AddSubgroup.closure_induction (p := fun v _ => σ • v = c • v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨χ, rfl⟩
      exact O.toricLift_inertia p hp.pos σ hσI c hσ χ
    · show σ • (0 : JZero (N₀ * p)) = c • (0 : JZero (N₀ * p))
      rw [nsmul_zero]
      exact map_zero (DistribMulAction.toAddMonoidHom (JZero (N₀ * p)) σ)
    · intro x y _ _ hx hy
      show σ • (x + y) = c • (x + y)
      rw [smul_add, nsmul_add, hx, hy]
    · intro x _ hx
      show σ • (-x) = c • (-x)
      rw [smul_neg, hx, neg_nsmul]
  have hinj : Nat.card ↥(O.toricPts p ⊓ W.toAddSubgroup) ≤ Nat.card ↥E := by
    haveI : Finite ↥E := inferInstance
    refine Nat.card_le_card_of_injective
      (fun v => (⟨⟨(v : JZero (N₀ * p)), v.2.2⟩, (hmemE _).mpr (htoric _ v.2.1)⟩ : ↥E)) ?_
    intro v v' h
    exact Subtype.ext (congrArg (fun e : ↥E => ((e : ↥W) : JZero (N₀ * p))) h)

  have hpk : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
    exact hp𝔪
  have hck : ((c : ℕ) : HeckeAlg ⧸ 𝔪) = -1 := by
    have hcv : c = p - 1 := by
      rw [hc, Units.val_neg, Units.val_one]
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
      subst hn
      rw [ZMod.val_neg_one, Nat.add_sub_cancel]
    rw [hcv, Nat.cast_sub hp.one_le, hpk, Nat.cast_one, zero_sub]
  have hEtop : E ≠ ⊤ := by
    intro htop
    have hρ : ρ = (c : HeckeAlg ⧸ 𝔪) • LinearMap.id := by
      rw [← sub_eq_zero]
      exact LinearMap.ker_eq_top.mp htop
    have hdet := det_mTorsionGaloisRep_eq_natCast_of_multiplicityOneData (N₀ * p) p 𝔪 ⟨h𝔪, hp𝔪, h2⟩ hsc σ c hσ
    have hdet' : LinearMap.det ρ = ((c : HeckeAlg ⧸ 𝔪)) ^ 2 := by
      rw [hρ, LinearMap.det_smul, LinearMap.det_id, mul_one, h2]
    have hcc : ((c : HeckeAlg ⧸ 𝔪)) ^ 2 = (c : HeckeAlg ⧸ 𝔪) := hdet'.symm.trans (by simpa [ρ] using hdet)
    rw [hck, neg_one_sq] at hcc

    have h2z : (2 : HeckeAlg ⧸ 𝔪) = 0 := by
      have := congrArg (· + 1) hcc
      simp only [neg_add_cancel] at this
      rw [← this]; norm_num
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    have : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 1 := by
      rw [hk]; push_cast; rw [h2z, zero_mul, zero_add]
    rw [hpk] at this
    exact zero_ne_one this
  have hfinE : Module.finrank (HeckeAlg ⧸ 𝔪) ↥E ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hle : Module.finrank (HeckeAlg ⧸ 𝔪) ↥E ≤ 2 := h2 ▸ Submodule.finrank_le E
    have heq : Module.finrank (HeckeAlg ⧸ 𝔪) ↥E = Module.finrank (HeckeAlg ⧸ 𝔪) ↥W := by
      rw [h2]; omega
    exact hEtop (Submodule.eq_top_of_finrank_eq heq)

  have hcardE : Nat.card ↥E ≤ Nat.card (HeckeAlg ⧸ 𝔪) := by
    rw [Module.natCard_eq_pow_finrank (K := HeckeAlg ⧸ 𝔪) (V := ↥E)]
    have hk1 : 1 ≤ Nat.card (HeckeAlg ⧸ 𝔪) := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    calc Nat.card (HeckeAlg ⧸ 𝔪) ^ Module.finrank (HeckeAlg ⧸ 𝔪) ↥E
        ≤ Nat.card (HeckeAlg ⧸ 𝔪) ^ 1 := Nat.pow_le_pow_right hk1 hfinE
      _ = Nat.card (HeckeAlg ⧸ 𝔪) := pow_one _
  exact hinj.trans hcardE

end S_ModularCurve_JZeroNeronObjectAtP_natCard_toricPts_inf_heckeTorsion_le
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_natCard_toricPts_inf_heckeTorsion_le (solution)
