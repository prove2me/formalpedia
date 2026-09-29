-- Prove2me | solution 1 for ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b3f53798-fd47-52e8-8c4b-413a004209b0

import Mathlib
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instIsElliptic_tateBase ModularCurve.numberField_of_finiteDimensional WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U"
p2m_attr_erase "simp" "CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty"
p2m_attr_erase "simp" "ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply"
p2m_attr_erase "simp" "ModularCurve.symPoly_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVectorLevel.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVectorLevel.mk.sizeOf_spec ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.JZeroNeronAtPData.mk.sizeOf_spec ModularCurve.JZeroNeronAtPData.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve~toricPoint ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace ATPSkel

open ModularCurve.JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}

theorem exists_algHom_valuationSubring_of_muCoord {t m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, χ = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA := by
  classical
  have hroot : ∀ g : Fin t → ZMod m, (χ (AddMonoidAlgebra.single g 1)) ^ m = 1 := by
    intro g
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have hg : m • g = 0 := by
      funext i
      show m • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hg]
    exact map_one χ
  have hmem : ∀ g : Fin t → ZMod m, χ (AddMonoidAlgebra.single g 1) ∈ A := by
    intro g
    have hint : IsIntegral ↥A (χ (AddMonoidAlgebra.single g 1)) := by
      refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hroot g, sub_self]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2
  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hmem _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd (g * h)) 1) =
          χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1) * χ (AddMonoidAlgebra.single (Multiplicative.toAdd h) 1)
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

omit [Fact p.Prime] in
theorem specMap_comp_genPt' (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

theorem specMap_decRestrict_comp_σA (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (dE : ↥A ≃+* ↥A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hdE : ∀ a : ↥A, ((dE a : ↥A) : AlgebraicClosure ℚ) = σ a) :
    Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA := by
  have hsub : A.subtype.comp dE.toRingHom = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
    RingHom.ext fun a => hdE a
  have hbar : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) := by
    rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hsub]
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← hbar, Category.assoc, Λ.hσA, specMap_comp_genPt']
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

section conv
variable {S' : Type} [CommRing S'] {L' : Type} [CommRing L'] [Algebra S' L'] {G' : Type} [AddMonoid G']

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (v : G') :
    (c * c') (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G') :
    (1 : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (n : ℕ) (v : G') :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_single, ih]

end conv

omit [Fact p.Prime] in

theorem hasEnoughRootsOfUnity_algebraicClosure (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (AlgebraicClosure ℚ) n := by
  refine ⟨?_, rootsOfUnity.isCyclic _ _⟩
  have hdeg : (Polynomial.cyclotomic n (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

end ATPSkel

open ModularCurve.JZeroNeronObjectAtP
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra
    ∀ (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (_ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
      (𝔓 : DRModelPackageLevel N₀ p hpN₀),
      (

      (let D : RelativePic0Designation (R p) (toBase N₀ p) :=
          ⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩
        ∃ (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
        (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
        (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

        (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

        (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
        (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
        (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
            (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
          Nonempty ((hDQ.poincare.pullbackAlong
              ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
                ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                  (Category.comp_id t)))).idealModule))

        (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
        (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
        (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

        (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
        (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
        (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection),

        (∀ x y : JZero (N₀ * p),
          O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)) ∧

      (∃ (ρ : R p →+* ↥A) (_ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
          (_ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
          (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
          (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
          (Rt : PlaceSpecialization.ProlongationTuple P) (_ : Rt.IsModel) (_ : Rt.RegularityLaw O.ssFinset)
          (_ : Rt.NodeValueLaw O.ssFinset) (_ : Rt.OrderLawFixed)
          (sp : ↥(inertiaInvariants A (N₀ * p)) →+
            GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset))
          (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) sp)

          (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀),

        O.frob = arithFrobC p (ResidueField ↥A) N₀ ∧

        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
                (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
                (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                  (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) ∧

        (∀ x : ↥(inertiaInvariants A (N₀ * p)),
          ExtendsToPlace A Λ.σA (O.pts (x : JZero (N₀ * p))) ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (x : JZero (N₀ * p))) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s))),
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s)))) =
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
              NeronModelInfra.schemeHomOverComp y O.torusFibre = toFibrePt (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s)) ↔
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x) = 0))) ∧

      (∀ (m : ℕ), m.Coprime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m) ∧
      (∀ (m : ℕ), 0 < m →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m)) →
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ p →
        ∀ (n : ℕ), ∀ x ∈ O.toricPts (p ^ n),
          φ • x ∈ O.toricPts (p ^ n) ∧
          (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • (φ • x) =
            (PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val • x ∧
          φ • ((heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • x) =
            (PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val • x := by
  intro Λ hJac O 𝔓 hbody φ hφ n x hx
  classical
  haveI hCh : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField (ResidueField ↥A)
  letI := heckeModuleBar (N₀ * p)
  have hφD : φ ∈ A.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup

  obtain ⟨φU, hφUmul, hφUpts⟩ := O.hecke (heckeGen ⟨p, Fact.out⟩)
  have hUop : ∀ y : JZero (N₀ * p), (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • y =
      O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts y) φU) := by
    intro y
    apply O.pts.injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    exact hφUpts y

  have hdE : ∃ dE : ↥A ≃+* ↥A, (∀ a : ↥A, dE a = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • a) :=
    ⟨MulSemiringAction.toRingEquiv _ _ (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)), fun a => rfl⟩
  obtain ⟨dE, hdEa⟩ := hdE
  have hres : (IsLocalRing.residue ↥A).comp dE.toRingHom = (frobenius (ResidueField ↥A) p).comp (IsLocalRing.residue ↥A) := by
    refine RingHom.ext fun a => ?_
    show IsLocalRing.residue ↥A (dE a) = (IsLocalRing.residue ↥A a) ^ p
    rw [hdEa, IsLocalRing.ResidueField.residue_smul]
    exact hφ.smul_residue_eq _
  have hdσ : Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA :=
    ATPSkel.specMap_decRestrict_comp_σA Λ dE φ (fun a => by rw [hdEa]; rfl)
  have hbase : Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by
    have h1 : resPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A := by
      rw [resPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hres]
    rw [← Category.assoc, ← h1, Category.assoc, hdσ]

  have hΞE : ∃ ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA),
      ΞG ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) := by
    refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [pullback.condition, Category.assoc, hbase]
  obtain ⟨ΞG, hΞ₁, hΞ₂⟩ := hΞE

  have hLA := ModularCurve.JZeroNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
    N₀ p hpN₀ A hA Λ hJac O (frobeniusEquiv (ResidueField ↥A) p) ΞG hΞ₁ hΞ₂
  obtain ⟨P₀, hP₀⟩ := hLA
  have hTS := ModularCurve.JZeroNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
    N₀ p hpN₀ A hA Λ hJac O φU (fun s x y => hφUmul s x y)
  obtain ⟨M₀, hM₀⟩ := hTS

  have hAWAY := ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne N₀ p hpN₀ A hA Λ hJac O 𝔓 hbody φ hφ
  have hUF : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hmk : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (φ • O.toricPoint (ℓ ^ k) hmk χ)) φU) = p • O.toricPoint (ℓ ^ k) hmk χ := by
    intro ℓ hℓ hℓp k hmk χ
    have hmemk := (ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      N₀ p hpN₀ A hA Λ hJac O (ℓ ^ k) hmk).2.2.1
    have h := (hAWAY ℓ hℓ hℓp k _ ((hmemk _).mpr ⟨χ, rfl⟩)).2.1
    rwa [hUop] at h
  have hFU : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hmk : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      φ • O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint (ℓ ^ k) hmk χ)) φU) = p • O.toricPoint (ℓ ^ k) hmk χ := by
    intro ℓ hℓ hℓp k hmk χ
    have hmemk := (ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      N₀ p hpN₀ A hA Λ hJac O (ℓ ^ k) hmk).2.2.1
    have h := (hAWAY ℓ hℓ hℓp k _ ((hmemk _).mpr ⟨χ, rfl⟩)).2.2
    rwa [hUop] at h
  have hLB := ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
    N₀ p hpN₀ A hA Λ hJac O ΞG hΞ₁ hΞ₂ P₀ hP₀ φU hφUmul M₀ hM₀ φ hφ hφD hUF hFU
  obtain ⟨hPM, hMP⟩ := hLB

  have hm : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hLD := ModularCurve.JZeroNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
    N₀ p hpN₀ A hA Λ hJac O ΞG hΞ₁ hΞ₂ P₀ hP₀ φ hφ hφD (p ^ n) hm
  obtain ⟨Pbar, hPbar, hLDχ⟩ := hLD
  have hTM := ModularCurve.JZeroNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
    N₀ p hpN₀ A hA Λ hJac O φU (fun s x y => hφUmul s x y) M₀ hM₀ (p ^ n) hm
  obtain ⟨Mbar, hMbar, hTMχ⟩ := hTM
  have hH1 := ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
    N₀ p hpN₀ A hA Λ hJac O (p ^ n) hm
  obtain ⟨hconv, -, hmem, -⟩ := hH1

  have hPMbar : Pbar.comp Mbar = AddMonoidHom.id _ ∧ Mbar.comp Pbar = AddMonoidHom.id _ := by
    haveI : NeZero (p ^ n) := ⟨hm.ne'⟩
    have hsurj : ∀ v : Fin O.toricRank → ZMod (p ^ n), ∃ z : Fin O.toricRank → ℤ,
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod (p ^ n))).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) z = v :=
      fun v => ⟨fun i => ((v i).cast : ℤ), funext fun i => by
        show (((v i).cast : ℤ) : ZMod (p ^ n)) = v i
        exact ZMod.intCast_zmod_cast (v i)⟩
    have hPbar' := fun z => DFunLike.congr_fun hPbar z
    have hMbar' := fun z => DFunLike.congr_fun hMbar z
    have hPM' := fun z => DFunLike.congr_fun hPM z
    have hMP' := fun z => DFunLike.congr_fun hMP z
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hPbar' hMbar' hPM' hMP'
    constructor
    · refine AddMonoidHom.ext fun v => ?_
      obtain ⟨z, rfl⟩ := hsurj v
      rw [AddMonoidHom.comp_apply, hMbar', hPbar', hPM', AddMonoidHom.id_apply]
    · refine AddMonoidHom.ext fun v => ?_
      obtain ⟨z, rfl⟩ := hsurj v
      rw [AddMonoidHom.comp_apply, hPbar', hMbar', hMP', AddMonoidHom.id_apply]

  have hUtor : ∀ χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ,
      (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • (O.toricPoint (p ^ n) hm χ) =
        O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
    intro χ
    rw [hUop]
    apply O.pts.injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    show (O.pts (O.pts.symm _)).1 ≫ φU.1 = (O.pts (O.pts.symm _)).1
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h := congrArg (fun w => w.1 ≫ pullback.fst O.g Λ.σA) (hTMχ χ)
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst] at h
    show (((muPt A O.toricRank (p ^ n) χ).1 ≫ (O.toricLift (p ^ n) hm).1) ≫ pullback.fst O.g Λ.σA) ≫ φU.1 =
      ((muPt A O.toricRank (p ^ n) (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ (O.toricLift (p ^ n) hm).1) ≫
        pullback.fst O.g Λ.σA
    simpa only [Category.assoc] using h

  have hcyc : ∀ (χ χφ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A),
      (∀ g : Fin O.toricRank → ZMod (p ^ n),
        χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1)) →
      χφ = χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
    intro χ χφ hχφ
    haveI hEn : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i =>
      haveI : NeZero (p ^ i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      ATPSkel.hasEnoughRootsOfUnity_algebraicClosure _
    refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro g
    rw [hχφ, AlgHom.comp_apply]
    have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)
        (AddMonoidAlgebra.single g (1 : ↥A)) = AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) 1 := by
      show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
      rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      rfl
    have hsp : AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) (1 : ↥A) =
        (AddMonoidAlgebra.single g (1 : ↥A)) ^ (((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) := by
      rw [AddMonoidAlgebra.single_pow, one_pow]
    rw [hmd, hsp, map_pow]
    set u : ↥A := χ (AddMonoidAlgebra.single g 1) with hu
    have hupow : u ^ (p ^ n) = 1 := by
      rw [hu, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have hg : (p ^ n) • g = 0 := by
        funext i
        show (p ^ n) • g i = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [hg]
      exact map_one χ
    apply Subtype.ext
    show φ (u : AlgebraicClosure ℚ) = ((u ^ _ : ↥A) : AlgebraicClosure ℚ)
    rw [SubmonoidClass.coe_pow]
    have hval : ((u : AlgebraicClosure ℚ)) ^ p ^ n = 1 := by
      rw [← SubmonoidClass.coe_pow, hupow]; rfl
    have hspec := cyclotomicCharacter.spec p (L := AlgebraicClosure ℚ) (n := n) φ.toRingEquiv (u : AlgebraicClosure ℚ) hval
    rw [show (φ.toRingEquiv : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (u : AlgebraicClosure ℚ) = φ (u : AlgebraicClosure ℚ) from rfl] at hspec
    rw [hspec]
    congr 1
    show (PadicInt.toZModPow n _).val = _
    rw [show PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) from rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]

  have hhom : ∀ (c : ℕ) (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _))) =
        c • O.toricPoint (p ^ n) hm χ := by
    intro c χ
    have hpow : χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _)) = ((WithConv.toConv χ) ^ c).ofConv := by
      refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
      intro g
      rw [AlgHom.comp_apply]
      have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _) (AddMonoidAlgebra.single g (1 : ↥A)) =
          AddMonoidAlgebra.single (c • g) 1 := by
        show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
        rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
        rfl
      rw [hmd, ← one_pow c, ← AddMonoidAlgebra.single_pow, map_pow, one_pow]
      exact (ATPSkel.convPow_apply_single (WithConv.toConv χ) c g).symm
    rw [hpow]
    have h1 : O.toricPoint (p ^ n) hm (1 : WithConv (muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have h := hconv 1 1
      rw [mul_one] at h
      exact left_eq_add.mp h
    have key : ∀ k : ℕ, O.toricPoint (p ^ n) hm ((WithConv.toConv χ) ^ k).ofConv = k • O.toricPoint (p ^ n) hm χ := by
      intro k
      induction k with
      | zero => rw [pow_zero, h1, zero_nsmul]
      | succ k ih => rw [pow_succ, hconv, ih, succ_nsmul]
    exact key c

  have hcomp : ∀ (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A) (f g : (Fin O.toricRank → ZMod (p ^ n)) →+ (Fin O.toricRank → ZMod (p ^ n))),
      ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A f))).comp
          (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A g) =
        (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (f.comp g))) := by
    intro χ f g
    rw [AddMonoidAlgebra.mapDomainAlgHom_comp]
    rfl

  have hval : (PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val = ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n := by
    rw [show PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) from rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]
  rw [hval]

  obtain ⟨χ, rfl⟩ := (hmem x).mp hx
  obtain ⟨χA, hχA⟩ := ATPSkel.exists_algHom_valuationSubring_of_muCoord (A := A) hm χ
  subst hχA
  obtain ⟨χφ, hχφ, hφι⟩ := hLDχ χA
  refine ⟨?_, ?_, ?_⟩
  · rw [hφι]
    exact (hmem _).mpr ⟨_, rfl⟩
  · rw [hφι, hUtor, hcomp, hPMbar.1, hcyc χA χφ hχφ, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.comp_id]
    exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
  · rw [hUtor]
    obtain ⟨χφ', hχφ', hφι'⟩ := hLDχ (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))
    have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
        (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := rfl
    rw [h3, hφι', hcyc _ χφ' hχφ']
    have hcm : ((χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
        ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _))).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar) =
        χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
      have hsw : Mbar.comp ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _) = ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _).comp Mbar := by
        refine AddMonoidHom.ext fun v => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_nsmul]
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
        ← AddMonoidHom.comp_assoc, hsw, AddMonoidHom.comp_assoc, hPMbar.2, AddMonoidHom.comp_id]
    rw [hcm]
    exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)

#print axioms solution

end S_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
end P2MW
export P2MW.S_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge (solution)
