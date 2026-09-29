-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.abq_heckeGen_smul_of_forall_reductionModL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4be563b4-f01e-5bd3-bb80-014939424dd5

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_mem_finPts_iff
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_smul_mem_finPts
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_smul_mem_toricPts
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeGen_smul_galois_smul
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_reductionModL_surjective
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_fixedPoints_frobSp_comp_self
import Theorems.Thm_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self
import Theorems.Thm_ModularCurve_jZero_zsmul_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_heckeGen_smul_of_forall_reductionModL_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm"
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace ABQH

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

omit [NeZero N₀] [NeZero p] in
theorem pos_of_coprime {M : ℕ} (hM : M.Coprime p) : 0 < M := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h
    rw [Nat.coprime_zero_left] at hM
    exact absurd hM (Fact.out : p.Prime).one_lt.ne'
  · exact h

omit [NeZero N₀] [NeZero p] in
theorem not_dvd_of_coprime {M : ℕ} (hM : M.Coprime p) : ¬ p ∣ M := fun h => by
  have h1 : p ∣ Nat.gcd M p := Nat.dvd_gcd h (dvd_refl p)
  rw [hM] at h1
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)

theorem eq_zero_of_nsmul_eq_zero_of_coprime {G : Type*} [AddCommGroup G] {a b : ℕ} (hab : a.Coprime b)
    (z : G) (ha : a • z = 0) (hb : b • z = 0) : z = 0 := by
  have h1 : addOrderOf z ∣ Nat.gcd a b :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero ha) (addOrderOf_dvd_of_nsmul_eq_zero hb)
  rw [hab.gcd_eq_one, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.mp h1

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem ext_unique_aux {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver Λ.σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA f) := by
    show IsSeparated (pullback.snd f Λ.σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr Λ.σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by first | exact z.2 | simpa using z.2 | simpa [barPt] using z.2
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f Λ.σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f Λ.σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem residue_eq_ptsSp_reductionModL (hpN₀ : ¬ p ∣ N₀) (hA : A.LiesOverPrime p) (hΛ : Λ.IsJacobian) (z : JZero N₀)
    (Q : SchemeHomOver Λ.σA Λ.f) (hQ : barPt A ≫ Q.1 = (Λ.pts z).1) :
    GoodReductionJacobian.schemeHomOverComp (resPt A) rfl Q = Λ.ptsSp (reductionModL A N₀ z) := by
  have hROP := hΛ.2.2.2.2.2.1 (reductionInputsModL_of_not_dvd N₀ hpN₀ A hA)
  haveI : IsSeparated Λ.f := by
    haveI : IsProper Λ.f := hΛ.1.proper
    infer_instance
  obtain ⟨P₀, hP₀gen, hP₀sp⟩ := hROP z
  have h1 : barPt A ≫ P₀.1 = (Λ.pts z).1 := congrArg Subtype.val hP₀gen
  have heq : Q = P₀ := ext_unique_aux _ _ (hQ.trans h1.symm)
  rw [heq]
  exact hP₀sp

theorem ptsSp_reductionModL_hecke (hpN₀ : ¬ p ∣ N₀) (hA : A.LiesOverPrime p) (hΛ : Λ.IsJacobian)
    (t : HeckeAlg) (φΛ : SchemeHomOver Λ.f Λ.f)
    (hφ : ∀ w : JZero N₀, (Λ.pts (letI := heckeModuleBar N₀; t • w)).1 = (Λ.pts w).1 ≫ φΛ.1) (w : JZero N₀) :
    Λ.ptsSp (reductionModL A N₀ (letI := heckeModuleBar N₀; t • w)) =
      NeronModelInfra.schemeHomOverComp (Λ.ptsSp (reductionModL A N₀ w)) φΛ := by
  have hROP := hΛ.2.2.2.2.2.1 (reductionInputsModL_of_not_dvd N₀ hpN₀ A hA)
  obtain ⟨P, hPgen, hPsp⟩ := hROP w
  have h1 : barPt A ≫ P.1 = (Λ.pts w).1 := congrArg Subtype.val hPgen
  have h2 : resPt A ≫ P.1 = (Λ.ptsSp (reductionModL A N₀ w)).1 := congrArg Subtype.val hPsp
  have h := residue_eq_ptsSp_reductionModL hpN₀ hA hΛ (letI := heckeModuleBar N₀; t • w) (NeronModelInfra.schemeHomOverComp P φΛ)
    (by rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, h1, hφ])
  rw [← h]
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, h2]

def Tbar (Λ : LevelData N₀ p A) (φΛ : SchemeHomOver Λ.f Λ.f) (u : JZeroC (ResidueField ↥A) N₀) : JZeroC (ResidueField ↥A) N₀ :=
  Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp (Λ.ptsSp u) φΛ)

theorem reductionModL_heckeOperatorBar (hpN₀ : ¬ p ∣ N₀) (hA : A.LiesOverPrime p) (hΛ : Λ.IsJacobian)
    (ℓ : Nat.Primes) (φΛ : SchemeHomOver Λ.f Λ.f)
    (hφ : ∀ w : JZero N₀, (Λ.pts (letI := heckeModuleBar N₀; heckeGen ℓ • w)).1 = (Λ.pts w).1 ≫ φΛ.1) (z : JZero N₀) :
    reductionModL A N₀ (heckeOperatorBar N₀ ℓ z) = Tbar Λ φΛ (reductionModL A N₀ z) := by
  rw [← heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar N₀)]
  apply Λ.ptsSp.injective
  rw [ptsSp_reductionModL_hecke hpN₀ hA hΛ (heckeGen ℓ) φΛ hφ z, Tbar, Equiv.apply_symm_apply]

theorem Tbar_add (hpN₀ : ¬ p ∣ N₀) (hA : A.LiesOverPrime p) (hΛ : Λ.IsJacobian)
    (ℓ : Nat.Primes) (φΛ : SchemeHomOver Λ.f Λ.f)
    (hφ : ∀ w : JZero N₀, (Λ.pts (letI := heckeModuleBar N₀; heckeGen ℓ • w)).1 = (Λ.pts w).1 ≫ φΛ.1)
    (u v : JZeroC (ResidueField ↥A) N₀) : Tbar Λ φΛ (u + v) = Tbar Λ φΛ u + Tbar Λ φΛ v := by
  have hsurj := reductionModL_surjective N₀ hpN₀ A hA
  obtain ⟨z₁, rfl⟩ := hsurj u
  obtain ⟨z₂, rfl⟩ := hsurj v
  rw [← map_add, ← reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ, map_add, map_add,
    reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ, reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ]

theorem Tbar_frobSp (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (ℓ : Nat.Primes) (φΛ : SchemeHomOver Λ.f Λ.f)
    (hφ : ∀ w : JZero N₀, (Λ.pts (letI := heckeModuleBar N₀; heckeGen ℓ • w)).1 = (Λ.pts w).1 ≫ φΛ.1)
    (u : JZeroC (ResidueField ↥A) N₀) : Tbar Λ φΛ (O.frobSp u) = O.frobSp (Tbar Λ φΛ u) := by
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat (Fact.out : p.Prime) hA
  obtain ⟨z, rfl⟩ := reductionModL_surjective N₀ hpN₀ A hA u
  rw [← O.frobSp_reductionModL σ hσ z, ← reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ,
    ← reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ, ← O.frobSp_reductionModL σ hσ,
    ← heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar N₀), ← heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar N₀),
    heckeGen_smul_galois_smul]

theorem reductionModL_degeneracy (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian) (i : Fin 2)
    (y : JZero (N₀ * p)) (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts y).1 = barPt A ≫ s.1) :
    Λ.ptsSp (reductionModL A N₀ (degeneracyPushforwardPair N₀ p i y)) =
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) (O.degeneracyHom i) := by
  have h := residue_eq_ptsSp_reductionModL hpN₀ hA hΛ (degeneracyPushforwardPair N₀ p i y)
    (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i))
    (by rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, ← hs, O.degeneracyHom_pts])
  rw [← h]
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem reductionModL_degeneracy_eq (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (y : JZero (N₀ * p)) (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts y).1 = barPt A ≫ s.1)
    (a₀ a₁ : JZeroC (ResidueField ↥A) N₀)
    (h0 : a₀ = Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))
    (h1 : a₁ = Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s))) :
    reductionModL A N₀ (degeneracyPushforwardPair N₀ p 0 y) = a₀ + O.frobSp a₁ ∧
    reductionModL A N₀ (degeneracyPushforwardPair N₀ p 1 y) = O.frobSp a₀ + a₁ := by
  obtain ⟨e0, e1⟩ := O.degeneracyHom_special (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)
  constructor
  · rw [← Equiv.symm_apply_apply Λ.ptsSp (reductionModL A N₀ _), reductionModL_degeneracy O hΛ 0 y s hs, e0, h0, h1]
  · rw [← Equiv.symm_apply_apply Λ.ptsSp (reductionModL A N₀ _), reductionModL_degeneracy O hΛ 1 y s hs, e1, h0, h1]

def Tfin (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian) (ℓ : Nat.Primes) (M : ℕ) (hM : 0 < M) :
    ↥(O.finPts M) →+ ↥(O.finPts M) :=
  letI := heckeModuleBar (N₀ * p)
  { toFun := fun y => ⟨heckeGen ℓ • (y : JZero (N₀ * p)),
      smul_mem_finPts N₀ p hpN₀ A hA Λ hΛ O M hM (heckeGen ℓ) (y : JZero (N₀ * p)) y.2⟩
    map_zero' := Subtype.ext (smul_zero _)
    map_add' := fun x y => Subtype.ext (smul_add _ _ _) }

theorem Tfin_coe (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian) (ℓ : Nat.Primes) (M : ℕ) (hM : 0 < M)
    (y : ↥(O.finPts M)) :
    ((Tfin O hΛ ℓ M hM y : ↥(O.finPts M)) : JZero (N₀ * p)) = (letI := heckeModuleBar (N₀ * p); heckeGen ℓ • (y : JZero (N₀ * p))) :=
  rfl

def TT (N₀ : ℕ) [NeZero N₀] (ℓ : Nat.Primes) : (JZero N₀ × JZero N₀) →+ (JZero N₀ × JZero N₀) :=
  AddMonoidHom.prodMap (heckeOperatorBar N₀ ℓ).toAddMonoidHom (heckeOperatorBar N₀ ℓ).toAddMonoidHom

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem TT_apply (ℓ : Nat.Primes) (v : JZero N₀ × JZero N₀) :
    TT N₀ ℓ v = (heckeOperatorBar N₀ ℓ v.1, heckeOperatorBar N₀ ℓ v.2) := rfl

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem TT_fst (ℓ : Nat.Primes) (v : JZero N₀ × JZero N₀) : (TT N₀ ℓ v).1 = heckeOperatorBar N₀ ℓ v.1 := rfl

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem TT_snd (ℓ : Nat.Primes) (v : JZero N₀ × JZero N₀) : (TT N₀ ℓ v).2 = heckeOperatorBar N₀ ℓ v.2 := rfl

def delta (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀))) (ℓ : Nat.Primes)
    (M : ℕ) (hM : M.Coprime p) : ↥(O.finPts M) →+ (JZero N₀ × JZero N₀) :=
  (abq M hM).comp (Tfin O hΛ ℓ M (pos_of_coprime hM)) - (TT N₀ ℓ).comp (abq M hM)

theorem delta_apply (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀))) (ℓ : Nat.Primes)
    (M : ℕ) (hM : M.Coprime p) (y : ↥(O.finPts M)) :
    delta O hΛ abq ℓ M hM y = abq M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) y) - TT N₀ ℓ (abq M hM y) := rfl

set_option maxHeartbeats 16000000 in
theorem key (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)))
    (habq : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)),
      abq m hm x ∈ Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ))
    (hformula : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
        reductionModL A N₀ (abq m hm x).1 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 0)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧
        reductionModL A N₀ (abq m hm x).2 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 1)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))
    (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ N₀ * p) :
    ∃ c : ℕ, 0 < c ∧ ∀ (M : ℕ) (hM : M.Coprime p) (y : ↥(O.finPts M)), c • delta O hΛ abq ℓ M hM y = 0 := by
  obtain ⟨c, hc, hcF⟩ :=
    AddMonoidHom.exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self O.frobSp
      (finite_fixedPoints_frobSp_comp_self N₀ p hpN₀ A hA Λ O)
  refine ⟨c, hc, fun M hM y => ?_⟩
  have hpM : ¬ p ∣ M := not_dvd_of_coprime hM
  have hinp := reductionInputsModL_of_not_dvd N₀ hpN₀ A hA
  have hℓp : ¬ (ℓ : ℕ) ∣ p := fun h => hℓ (Dvd.dvd.mul_left h N₀)
  obtain ⟨φΛ, -, hφ⟩ := hΛ.2.2.2.2.2.2 (heckeGen ℓ)

  obtain ⟨a, ha⟩ : ∃ a, abq M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) y) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, abq M hM y = b := ⟨_, rfl⟩
  have ht : M • b.1 = 0 ∧ M • b.2 = 0 := by
    have h := habq M hM y
    rw [hb, Submodule.mem_torsionBy_iff, natCast_zsmul, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero] at h
    exact h
  have ht' : M • a.1 = 0 ∧ M • a.2 = 0 := by
    have h := habq M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) y)
    rw [ha, Submodule.mem_torsionBy_iff, natCast_zsmul, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero] at h
    exact h
  have hTt : ∀ w : JZero N₀, M • w = 0 → M • (heckeOperatorBar N₀ ℓ w) = 0 := fun w hw => by
    rw [← map_nsmul, hw, map_zero]

  obtain ⟨-, s, hs⟩ := (mem_finPts_iff O M (y : JZero (N₀ * p))).mp y.2
  obtain ⟨-, s', hs'⟩ := (mem_finPts_iff O M ((Tfin O hΛ ℓ M (pos_of_coprime hM) y : ↥(O.finPts M)) : JZero (N₀ * p))).mp
    (Tfin O hΛ ℓ M (pos_of_coprime hM) y).2
  obtain ⟨f0, f1⟩ := hformula M hM y s hs
  obtain ⟨g0, g1⟩ := hformula M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) y) s' hs'
  rw [hb] at f0 f1
  rw [ha] at g0 g1

  obtain ⟨r0, r1⟩ := reductionModL_degeneracy_eq O hΛ (y : JZero (N₀ * p)) s hs _ _ f0 f1
  obtain ⟨r0', r1'⟩ := reductionModL_degeneracy_eq O hΛ
    ((Tfin O hΛ ℓ M (pos_of_coprime hM) y : ↥(O.finPts M)) : JZero (N₀ * p)) s' hs' _ _ g0 g1

  have c1 : ∀ i : Fin 2, degeneracyPushforwardPair N₀ p i ((Tfin O hΛ ℓ M (pos_of_coprime hM) y : ↥(O.finPts M)) : JZero (N₀ * p)) =
      heckeOperatorBar N₀ ℓ (degeneracyPushforwardPair N₀ p i (y : JZero (N₀ * p))) := fun i => by
    rw [Tfin_coe, heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar (N₀ * p))]
    exact degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd N₀ p (heckeInputsAll (N₀ * p)) (heckeInputsAll N₀) ℓ
      hℓp i _

  have hTr : ∀ z : JZero N₀, reductionModL A N₀ (heckeOperatorBar N₀ ℓ z) = Tbar Λ φΛ (reductionModL A N₀ z) :=
    reductionModL_heckeOperatorBar hpN₀ hA hΛ ℓ φΛ hφ
  have hTadd := Tbar_add hpN₀ hA hΛ ℓ φΛ hφ
  have hTF := Tbar_frobSp O hΛ ℓ φΛ hφ

  have E0 : reductionModL A N₀ a.1 + O.frobSp (reductionModL A N₀ a.2) =
      reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.1) + O.frobSp (reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.2)) := by
    rw [← r0', c1 0, hTr, r0, hTadd, hTF, ← hTr, ← hTr]
  have E1 : O.frobSp (reductionModL A N₀ a.1) + reductionModL A N₀ a.2 =
      O.frobSp (reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.1)) + reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.2) := by
    rw [← r1', c1 1, hTr, r1, hTadd, hTF, ← hTr, ← hTr]
  have e0 : reductionModL A N₀ (a.1 - heckeOperatorBar N₀ ℓ b.1) +
      O.frobSp (reductionModL A N₀ (a.2 - heckeOperatorBar N₀ ℓ b.2)) = 0 := by
    have h : reductionModL A N₀ (a.1 - heckeOperatorBar N₀ ℓ b.1) +
        O.frobSp (reductionModL A N₀ (a.2 - heckeOperatorBar N₀ ℓ b.2)) =
        (reductionModL A N₀ a.1 + O.frobSp (reductionModL A N₀ a.2)) -
          (reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.1) + O.frobSp (reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.2))) := by
      rw [map_sub, map_sub, map_sub]; abel
    rw [h, sub_eq_zero]
    exact E0
  have e1 : O.frobSp (reductionModL A N₀ (a.1 - heckeOperatorBar N₀ ℓ b.1)) +
      reductionModL A N₀ (a.2 - heckeOperatorBar N₀ ℓ b.2) = 0 := by
    have h : O.frobSp (reductionModL A N₀ (a.1 - heckeOperatorBar N₀ ℓ b.1)) +
        reductionModL A N₀ (a.2 - heckeOperatorBar N₀ ℓ b.2) =
        (O.frobSp (reductionModL A N₀ a.1) + reductionModL A N₀ a.2) -
          (O.frobSp (reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.1)) + reductionModL A N₀ (heckeOperatorBar N₀ ℓ b.2)) := by
      rw [map_sub, map_sub, map_sub]; abel
    rw [h, sub_eq_zero]
    exact E1
  obtain ⟨k0, k1⟩ := hcF _ _ e0 e1

  rw [delta_apply, ha, hb]
  refine Prod.ext ?_ ?_
  · rw [Prod.smul_fst, Prod.fst_zero, Prod.fst_sub, TT_fst]
    refine eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp M hpM _ ?_ ?_
    · rw [← mul_nsmul', Nat.mul_comm, mul_nsmul', nsmul_sub, ht'.1, hTt _ ht.1, sub_zero, smul_zero]
    · rw [map_nsmul]; exact k0
  · rw [Prod.smul_snd, Prod.snd_zero, Prod.snd_sub, TT_snd]
    refine eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N₀ hpN₀ A hA hinp M hpM _ ?_ ?_
    · rw [← mul_nsmul', Nat.mul_comm, mul_nsmul', nsmul_sub, ht'.2, hTt _ ht.2, sub_zero, smul_zero]
    · rw [map_nsmul]; exact k1

theorem delta_eq_zero_of_mem_toricPts (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀))) (ℓ : Nat.Primes)
    (hker : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)), abq m hm x = 0 ↔ (x : JZero (N₀ * p)) ∈ O.toricPts m)
    (M : ℕ) (hM : M.Coprime p) (t : ↥(O.finPts M)) (ht : (t : JZero (N₀ * p)) ∈ O.toricPts M) :
    delta O hΛ abq ℓ M hM t = 0 := by
  have h1 : abq M hM t = 0 := (hker M hM t).mpr ht
  have h2 : abq M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) t) = 0 :=
    (hker M hM _).mpr (smul_mem_toricPts N₀ p hpN₀ A hA Λ hΛ O M (pos_of_coprime hM) (heckeGen ℓ) _ ht)
  rw [delta_apply, h1, h2, map_zero, sub_zero]

set_option maxHeartbeats 16000000 in
theorem delta_compat (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (hΛ : Λ.IsJacobian)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀))) (ℓ : Nat.Primes)
    (hcompat : ∀ (m m' : ℕ) (hm : m.Coprime p) (hm' : m'.Coprime p) (h : m ∣ m') (x : ↥(O.finPts m))
      (hx : (x : JZero (N₀ * p)) ∈ O.finPts m'), abq m' hm' ⟨x, hx⟩ = abq m hm x)
    (m M : ℕ) (hm : m.Coprime p) (hM : M.Coprime p) (hmM : m ∣ M) (c : ℕ) (x' : ↥(O.finPts M)) (w : ↥(O.finPts m))
    (hw : (w : JZero (N₀ * p)) = c • (x' : JZero (N₀ * p))) :
    delta O hΛ abq ℓ m hm w = c • delta O hΛ abq ℓ M hM x' := by
  have hwM : (w : JZero (N₀ * p)) ∈ O.finPts M := by
    rw [hw]; exact (O.finPts M).nsmul_mem x'.2 c
  have hx1 : (⟨(w : JZero (N₀ * p)), hwM⟩ : ↥(O.finPts M)) = c • x' :=
    Subtype.ext (hw.trans (AddSubmonoidClass.coe_nsmul x' c).symm)
  have hTmem : ((Tfin O hΛ ℓ m (pos_of_coprime hm) w : ↥(O.finPts m)) : JZero (N₀ * p)) ∈ O.finPts M := by
    rw [Tfin_coe, hw, ← AddSubmonoidClass.coe_nsmul]
    exact (Tfin O hΛ ℓ M (pos_of_coprime hM) (c • x')).2
  have hx2 : (⟨_, hTmem⟩ : ↥(O.finPts M)) = Tfin O hΛ ℓ M (pos_of_coprime hM) (c • x') := by
    apply Subtype.ext
    show ((Tfin O hΛ ℓ m (pos_of_coprime hm) w : ↥(O.finPts m)) : JZero (N₀ * p)) =
      ((Tfin O hΛ ℓ M (pos_of_coprime hM) (c • x') : ↥(O.finPts M)) : JZero (N₀ * p))
    rw [Tfin_coe, Tfin_coe, hw, AddSubmonoidClass.coe_nsmul]
  rw [← map_nsmul, delta_apply, delta_apply, ← hx2, ← hx1, hcompat m M hm hM hmM w hwM,
    hcompat m M hm hM hmM _ hTmem]

end ABQH

set_option maxHeartbeats 16000000 in
open ABQH in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)))
    (habq : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)),
      abq m hm x ∈ Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ))
    (hformula : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
        reductionModL A N₀ (abq m hm x).1 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 0)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧
        reductionModL A N₀ (abq m hm x).2 =
          Λ.ptsSp.symm (fibreMap (O.abqFibre 1)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)))
    (hker : ∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)), abq m hm x = 0 ↔ (x : JZero (N₀ * p)) ∈ O.toricPts m)
    (hrange : ∀ (m : ℕ) (hm : m.Coprime p),
      (abq m hm).range = (Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ)).toAddSubgroup)
    (hcompat : ∀ (m m' : ℕ) (hm : m.Coprime p) (hm' : m'.Coprime p) (h : m ∣ m') (x : ↥(O.finPts m))
      (hx : (x : JZero (N₀ * p)) ∈ O.finPts m'), abq m' hm' ⟨x, hx⟩ = abq m hm x)
    (m : ℕ) (hm : m.Coprime p) (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ N₀ * p) (x : ↥(O.finPts m))
    (hx : (letI := heckeModuleBar (N₀ * p); heckeGen ℓ • (x : JZero (N₀ * p))) ∈ O.finPts m) :
    abq m hm ⟨_, hx⟩ = (letI := heckeModuleBar N₀; (heckeGen ℓ • (abq m hm x).1, heckeGen ℓ • (abq m hm x).2)) := by

  obtain ⟨c, hc, hkey⟩ := key O hΛ abq habq hformula ℓ hℓ
  have hpp : p.Prime := Fact.out
  obtain ⟨c', hc'0, hc'p, k, hcc⟩ : ∃ c' : ℕ, 0 < c' ∧ c'.Coprime p ∧ ∃ k : ℕ, p ^ k * c' = c :=
    ⟨c / p ^ c.factorization p, Nat.ordCompl_pos p hc.ne', (Nat.coprime_ordCompl hpp hc.ne').symm,
      c.factorization p, Nat.ordProj_mul_ordCompl_eq_self c p⟩
  have hkey' : ∀ (M : ℕ) (hM : M.Coprime p) (y : ↥(O.finPts M)), c' • delta O hΛ abq ℓ M hM y = 0 := by
    intro M hM y
    have hMt : M • delta O hΛ abq ℓ M hM y = 0 := by
      have ht := habq M hM y
      have ht' := habq M hM (Tfin O hΛ ℓ M (pos_of_coprime hM) y)
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at ht ht'
      rw [delta_apply, nsmul_sub, ht', ← map_nsmul, ht, map_zero, sub_zero]
    refine eq_zero_of_nsmul_eq_zero_of_coprime (Nat.Coprime.pow_right k hM).symm _ ?_ ?_
    · rw [← mul_nsmul', hcc]; exact hkey M hM y
    · rw [← mul_nsmul', Nat.mul_comm, mul_nsmul', hMt, smul_zero]

  have hM : (c' * m).Coprime p := Nat.Coprime.mul_left hc'p hm
  have hmM : m ∣ c' * m := Dvd.intro_left c' rfl
  have hc'z : (c' : ℤ) ≠ 0 := by exact_mod_cast hc'0.ne'
  obtain ⟨z1, hz1⟩ := jZero_zsmul_surjective N₀ (c' : ℤ) hc'z (abq m hm x).1
  obtain ⟨z2, hz2⟩ := jZero_zsmul_surjective N₀ (c' : ℤ) hc'z (abq m hm x).2
  have hz : (c' : ℤ) • ((z1, z2) : JZero N₀ × JZero N₀) = abq m hm x := Prod.ext hz1 hz2
  have hzM : ((z1, z2) : JZero N₀ × JZero N₀) ∈ (abq (c' * m) hM).range := by
    rw [hrange (c' * m) hM, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, Nat.cast_mul c' m, mul_comm (c' : ℤ) (m : ℤ),
      mul_smul, hz]
    exact (Submodule.mem_torsionBy_iff _ _).mp (habq m hm x)
  obtain ⟨x', hx'⟩ := hzM
  have hwM : c' • (x' : JZero (N₀ * p)) ∈ O.finPts (c' * m) := (O.finPts (c' * m)).nsmul_mem x'.2 c'
  have hwm : c' • (x' : JZero (N₀ * p)) ∈ O.finPts m := by
    rw [mem_finPts_iff] at hwM ⊢
    refine ⟨?_, hwM.2⟩
    have h1 := ((mem_finPts_iff O (c' * m) (x' : JZero (N₀ * p))).mp x'.2).1
    change _ ∈ (Submodule.torsionBy ℤ (JZero (N₀ * p)) ((c' * m : ℕ) : ℤ)).toAddSubgroup at h1
    change _ ∈ (Submodule.torsionBy ℤ (JZero (N₀ * p)) (m : ℤ)).toAddSubgroup
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul] at h1 ⊢
    rw [← mul_nsmul', Nat.mul_comm m c', h1]
  have hab : abq m hm ⟨c' • (x' : JZero (N₀ * p)), hwm⟩ = abq m hm x := by
    rw [← hcompat m (c' * m) hm hM hmM ⟨c' • (x' : JZero (N₀ * p)), hwm⟩ hwM]
    have h : (⟨c' • (x' : JZero (N₀ * p)), hwM⟩ : ↥(O.finPts (c' * m))) = c' • x' :=
      Subtype.ext (AddSubmonoidClass.coe_nsmul x' c').symm
    rw [h, map_nsmul, hx', ← natCast_zsmul, hz]
  have htor : (((⟨c' • (x' : JZero (N₀ * p)), hwm⟩ : ↥(O.finPts m)) - x : ↥(O.finPts m)) : JZero (N₀ * p)) ∈ O.toricPts m :=
    (hker m hm _).mp (by rw [map_sub, hab, sub_self])

  have hδ : delta O hΛ abq ℓ m hm x = 0 := by
    have e := map_sub (delta O hΛ abq ℓ m hm) ⟨c' • (x' : JZero (N₀ * p)), hwm⟩ x
    rw [delta_eq_zero_of_mem_toricPts O hΛ abq ℓ hker m hm _ htor,
      delta_compat O hΛ abq ℓ hcompat m (c' * m) hm hM hmM c' x' ⟨c' • (x' : JZero (N₀ * p)), hwm⟩ rfl,
      hkey' (c' * m) hM x', eq_comm, sub_eq_zero] at e
    exact e.symm

  rw [delta_apply, sub_eq_zero, TT_apply] at hδ
  refine hδ.trans (Prod.ext ?_ ?_)
  · exact (heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar N₀) ℓ _).symm
  · exact (heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar N₀) ℓ _).symm

end

end S_ModularCurve_JZeroNeronObjectAtP_abq_heckeGen_smul_of_forall_reductionModL_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_abq_heckeGen_smul_of_forall_reductionModL_eq (solution)
