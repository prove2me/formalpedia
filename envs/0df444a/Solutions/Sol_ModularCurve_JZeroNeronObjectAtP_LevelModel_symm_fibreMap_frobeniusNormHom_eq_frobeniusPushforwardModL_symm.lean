-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.LevelModel.symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d4da4d9f-622f-563a-82f4-feeb20057e9e

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ReductionModL
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange
import Theorems.Thm_ModularCurve_reductionModL_surjective
import Theorems.Thm_ModularCurve_reductionModL_smul_of_isFrobeniusAt
import Theorems.Thm_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_classifies_rigidify_normModule
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_charP
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff"
p2m_attr_erase "simp" "ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel IsLocalRing

namespace FROBDICT

open ModularCurve.JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime]

noncomputable def curveFibrePt {A : ValuationSubring (AlgebraicClosure ℚ)} (M : LevelModel N₀ p A)
    (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p)) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)) :=
  letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
  pullback.lift (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1) (𝟙 _) (by
    rw [Category.assoc, xA.2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

noncomputable def ajFibre {A : ValuationSubring (AlgebraicClosure ℚ)} (M : LevelModel N₀ p A) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)) ⟶ (M.D₀.baseChange (ResidueField ↥A)).P :=
  letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
  pullback.map _ _ _ _ M.aj₀.1 (𝟙 _) (𝟙 _) (by rw [M.aj₀.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

theorem toFibrePt_coe {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) :
    (ModularCurve.JZeroNeronObjectAtP.toFibrePt x).1 =
      pullback.lift x.1 (𝟙 _) ((ModularCurve.JZeroNeronObjectAtP.overId x).2) := rfl

theorem fibreMap_coe {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι f))
    (x : SchemeHomOver ι g) :
    (ModularCurve.JZeroNeronObjectAtP.fibreMap φ x).1 =
      ((ModularCurve.JZeroNeronObjectAtP.toFibrePt x).1 ≫ φ.1) ≫ pullback.fst f ι := rfl

theorem castOver_mul {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (x y : SchemeHomOver ι f) :
    castOver h (L.mul ι x y) = L.mul ι' (castOver h x) (castOver h y) := by
  subst h; rfl

theorem fibreMap_eq {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι f))
    (x : SchemeHomOver ι g) :
    ModularCurve.JZeroNeronObjectAtP.fibreMap φ x =
      castOver (Category.id_comp ι) (RelativeGroupLaw.baseChangePointToBase ι
        (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase ι (castOver (Category.id_comp ι).symm x)) φ)) := rfl

theorem mul_left_cancel {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t f)
    (h : L.mul t x y = L.mul t x z) : y = z := by
  rw [← L.one_mul t y, ← L.one_mul t z, ← L.inv_mul_cancel t x, L.mul_assoc, L.mul_assoc, h]

end FROBDICT

p2m_open "P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm.FROBDICT ModularCurve.JZeroNeronObjectAtP CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 6400000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p]

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hΛ : M.toLevelData.IsJacobian) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    letI := instDecidableEqResidueFieldSemistable A
    ∀
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀))
        (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))

      (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
      (_ : φκ = 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A)))
      (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
      [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (_ : ∀ x, φκ.finrank x = p)

      (F : SchemeHomOver (M.D₀.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
          (b : SchemeHomOver t (M.D₀.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t
              (sectionBaseChange (ResidueField ↥A) M.ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
            (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

      (e : JZeroC (ResidueField ↥A) N₀ ≃ SchemeHomOver (specMap (R p) (ResidueField ↥A)) M.D₀.toBase)
      (_ : ∀ u : JZeroC (ResidueField ↥A) N₀, (e u).1 = (M.ptsSp u).1)
      (b : SchemeHomOver (specMap (R p) (ResidueField ↥A)) M.D₀.toBase),
      e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap F b) = frobeniusPushforwardModL (ResidueField ↥A) N₀ p (e.symm b) := by
  intro hD₀κ hP₀κ φκ hφκ hφκ_over _ _ _ hrk F hF e he b
  letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
  letI := instDecidableEqResidueFieldSemistable A
  haveI := M.proper₀

  have hseam : resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ) = specMap (R p) (ResidueField ↥A) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he' : ∀ u, e u = castOver hseam (M.ptsSp u) := fun u => Subtype.ext (he u)

  have hRI : ReductionInputsModL A N₀ := ModularCurve.reductionInputsModL_of_not_dvd N₀ hpN₀ A hA
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime (Fact.out) A hA
  obtain ⟨u, rfl⟩ : ∃ u, e u = b := ⟨e.symm b, e.apply_symm_apply b⟩
  rw [Equiv.symm_apply_apply]
  obtain ⟨y, rfl⟩ := ModularCurve.reductionModL_surjective N₀ hpN₀ A hA u

  rw [← ModularCurve.reductionModL_smul_of_isFrobeniusAt N₀ A hRI σ hσ y, Equiv.symm_apply_eq]

  have hlaw : RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) hD₀κ =
      M.law.baseChange (specMap (R p) (ResidueField ↥A)) :=
    AlgebraicGeometry.RelPicard.relativeGroupLaw_baseChange_eq (R p) (toBase0 N₀ p) M.ε₀ M.D₀ M.rep (ResidueField ↥A) hD₀κ hP₀κ
  obtain ⟨hFadd, -⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.comp_mul_eq_mul_comp_of_classifies_rigidify_normModule
    hD₀κ hD₀κ φκ hφκ_over p hrk F hF
  have e_add : ∀ u v, e (u + v) = M.law.mul _ (e u) (e v) := by
    intro u v
    have h5 : M.ptsSp (u + v) = M.law.mul _ (M.ptsSp u) (M.ptsSp v) := hΛ.2.2.2.2.1 u v
    rw [he', he', he', h5, FROBDICT.castOver_mul]
  have fm_add : ∀ a b : SchemeHomOver (specMap (R p) (ResidueField ↥A)) M.D₀.toBase,
      ModularCurve.JZeroNeronObjectAtP.fibreMap F (M.law.mul _ a b) =
        M.law.mul _ (ModularCurve.JZeroNeronObjectAtP.fibreMap F a) (ModularCurve.JZeroNeronObjectAtP.fibreMap F b) := by
    intro a b
    rw [FROBDICT.fibreMap_eq, FROBDICT.fibreMap_eq, FROBDICT.fibreMap_eq, ← FROBDICT.castOver_mul]
    congr 1
    rw [FROBDICT.castOver_mul M.law, ← RelativeGroupLaw.baseChangePointToBase_mul, ← hlaw, ← hFadd (𝟙 _), hlaw,
      RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase]

  have add₁ : ∀ y y' : JZero N₀,
      ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ (y + y'))) =
        M.law.mul _ (ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ y)))
          (ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ y'))) := by
    intro y y'; rw [map_add, e_add, fm_add]
  have add₂ : ∀ y y' : JZero N₀,
      e (reductionModL A N₀ (σ • (y + y'))) = M.law.mul _ (e (reductionModL A N₀ (σ • y))) (e (reductionModL A N₀ (σ • y'))) := by
    intro y y'; rw [smul_add, map_add, e_add]

  let s₀' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback (IgusaScheme.igusaTo N₀ p) (genPt p) :=
    pullback.lift (genPt p ≫ M.ε₀.1) (𝟙 _) (by rw [Category.assoc, M.ε₀.2, Category.comp_id, Category.id_comp])
  let s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _} :=
    ⟨s₀' ≫ inv M.eeta₀, by rw [Category.assoc, ← M.heeta₀, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩
  have hs₀ : s₀.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ M.ε₀.1 := by
    show (s₀' ≫ inv M.eeta₀) ≫ M.eeta₀ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  suffices core : ∀ (x : SchemeHomOver (genPt p) (toBase0 N₀ p)) (y₀ : JZero N₀), (M.pts y₀).1 = x.1 ≫ M.aj₀.1 →
      ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ y₀)) = e (reductionModL A N₀ (σ • y₀)) by

    have h1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀), v.deg = 1 :=
      fun v => AlgebraicCurve.Place.deg_eq_one_of_isRational (ModularCurve.isRational_place_modularFunctionFieldBar N₀ v)
    have hgen := AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single h1 (M.Meta₀.pointEquivPlace s₀) y
    refine AddSubgroup.closure_induction (p := fun y _ =>
      ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ y)) = e (reductionModL A N₀ (σ • y))) ?_ ?_ ?_ ?_ hgen
    ·
      rintro _ ⟨V, hV, rfl⟩
      try dsimp only
      obtain ⟨Dv, hDv, hpts⟩ := M.pts_aj (M.Meta₀.pointEquivPlace.symm V) s₀ hs₀
      have hDv' : (⟨Finsupp.single V (1 : ℤ) - Finsupp.single (M.Meta₀.pointEquivPlace s₀) 1, hV⟩ :
          AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N₀))) = Dv := by
        apply Subtype.ext; rw [hDv, Equiv.apply_symm_apply]
      rw [hDv']
      refine core ⟨(M.Meta₀.pointEquivPlace.symm V).1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p), ?_⟩ _ ?_
      · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc M.eeta₀, M.heeta₀,
          ← Category.assoc, (M.Meta₀.pointEquivPlace.symm V).2, Category.id_comp]
      · rw [hpts]; simp only [Category.assoc]
    ·
      try dsimp only
      have z₁ := add₁ 0 0
      have z₂ := add₂ 0 0
      rw [add_zero] at z₁ z₂
      have k₁ := FROBDICT.mul_left_cancel M.law _ _ _ _ ((M.law.mul_one _ _).trans z₁)
      have k₂ := FROBDICT.mul_left_cancel M.law _ _ _ _ ((M.law.mul_one _ _).trans z₂)
      rw [← k₁, ← k₂]
    ·
      intro y y' _ _ hy hy'
      try dsimp only at hy hy' ⊢
      rw [add₁, add₂, hy, hy']
    ·
      intro y _ hy
      try dsimp only at hy ⊢
      have n₁ := add₁ y (-y)
      have n₂ := add₂ y (-y)
      rw [add_neg_cancel] at n₁ n₂

      have z₁ := add₁ 0 0
      have z₂ := add₂ 0 0
      rw [add_zero] at z₁ z₂
      have k₁ := FROBDICT.mul_left_cancel M.law _ _ _ _ ((M.law.mul_one _ _).trans z₁)
      have k₂ := FROBDICT.mul_left_cancel M.law _ _ _ _ ((M.law.mul_one _ _).trans z₂)
      have h0 : ModularCurve.JZeroNeronObjectAtP.fibreMap F (e (reductionModL A N₀ 0)) = e (reductionModL A N₀ (σ • 0)) := by
        rw [← k₁, ← k₂]
      rw [h0, hy] at n₁
      exact FROBDICT.mul_left_cancel M.law _ _ _ _ (n₁.symm.trans n₂)
  intro x y₀ hy₀

  obtain ⟨xA, hxA⟩ := ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper p A M.ρ M.hρ (toBase0 N₀ p) x
  have hσgen : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
    rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact σ.commutes r
  let xσ : SchemeHomOver (genPt p) (toBase0 N₀ p) :=
    ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1, by rw [Category.assoc, x.2, hσgen]⟩
  obtain ⟨zA, hzA⟩ := ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper p A M.ρ M.hρ (toBase0 N₀ p) xσ

  let bA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase :=
    ⟨xA.1 ≫ M.aj₀.1, by rw [Category.assoc, M.aj₀.2, xA.2]⟩
  let cA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase :=
    ⟨zA.1 ≫ M.aj₀.1, by rw [Category.assoc, M.aj₀.2, zA.2]⟩
  have hbA : barPt A ≫ bA.1 = (M.pts y₀).1 := by
    show barPt A ≫ xA.1 ≫ M.aj₀.1 = _
    rw [← Category.assoc, hxA, hy₀]
  have hcA : barPt A ≫ cA.1 = (M.pts (σ • y₀)).1 := by
    have hg : (M.pts (σ • y₀)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (M.pts y₀).1 :=
      hΛ.2.2.2.1 σ y₀
    show barPt A ≫ zA.1 ≫ M.aj₀.1 = _
    rw [← Category.assoc, hzA, hg, hy₀]
    show (Spec.map _ ≫ x.1) ≫ M.aj₀.1 = _
    rw [Category.assoc]
  have hred₁ : e (reductionModL A N₀ y₀) = castOver hseam (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl bA) := by
    rw [he', ← ModularCurve.JZeroNeronObjectAtP.LevelModel.ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
      N₀ p hpN₀ A hA M hΛ y₀ bA hbA]
    exact congrArg (castOver hseam) (M.toLevelData.ptsSp.apply_symm_apply _)
  have hred₂ : e (reductionModL A N₀ (σ • y₀)) = castOver hseam (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl cA) := by
    rw [he', ← ModularCurve.JZeroNeronObjectAtP.LevelModel.ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
      N₀ p hpN₀ A hA M hΛ (σ • y₀) cA hcA]
    exact congrArg (castOver hseam) (M.toLevelData.ptsSp.apply_symm_apply _)
  rw [hred₁, hred₂]

  have hφ : 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A)) = φκ :=
    hφκ.symm
  have hz : curveFibrePt M zA = curveFibrePt M xA ≫ φκ := by
    rw [← hφ]
    exact ModularCurve.JZeroNeronObjectAtP.LevelModel.fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt N₀ p hpN₀ 𝔓 A hA M σ hσ
      xA zA (by rw [hzA]; show Spec.map _ ≫ x.1 = _; rw [hxA])

  haveI hsep : IsSeparated (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_charP N₀ p hpN₀ (ResidueField ↥A)
      (algebraMap (R p) (ResidueField ↥A))
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
      (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) := inferInstance

  have hcf : ∀ (wA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p)),
      curveFibrePt M wA ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ :=
    fun wA => pullback.lift_snd _ _ _
  have haj_over : ajFibre M ≫ (M.D₀.baseChange (ResidueField ↥A)).toBase = baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) := by
    rw [FROBDICT.ajFibre, pullback.lift_snd, Category.comp_id]

  let yy : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    ⟨curveFibrePt M xA, hcf xA⟩
  let xb : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    ⟨(𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1) ≫ φκ, by
      rw [Category.assoc, hφκ_over, Category.id_comp]; exact (sectionBaseChange (ResidueField ↥A) M.ε₀).2⟩
  let xg : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    ⟨curveFibrePt M xA ≫ φκ, by rw [Category.assoc, hφκ_over]; exact hcf xA⟩

  let pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (M.D₀.baseChange (ResidueField ↥A)).toBase :=
    fun w => ⟨w.1 ≫ ajFibre M, by rw [Category.assoc, haj_over]; exact w.2⟩
  have AJ := ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint N₀ p hpN₀ A M
    hD₀κ hP₀κ

  have key := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
    hD₀κ hD₀κ φκ hφκ_over p hrk F hF (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) yy xb xg rfl rfl
    (pt yy) (AJ yy) (pt xb) (pt xg) (AJ xb) (AJ xg)

  have hb1 : (pt xb).1 = (M.D₀.baseChange (ResidueField ↥A)).zeroSection := by
    show ((𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1) ≫ φκ) ≫ ajFibre M = _

    have hε : (sectionBaseChange (ResidueField ↥A) M.ε₀).1 ≫ φκ = (sectionBaseChange (ResidueField ↥A) M.ε₀).1 := by
      let εA : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p) :=
        ⟨Spec.map (CommRingCat.ofHom M.ρ) ≫ M.ε₀.1, by rw [Category.assoc, M.ε₀.2, Category.comp_id]⟩
      have hgen : barPt A ≫ Spec.map (CommRingCat.ofHom M.ρ) ≫ M.ε₀.1 = genPt p ≫ M.ε₀.1 := by
        rw [← Category.assoc, M.barPt_σA]
      have hεconj : barPt A ≫ εA.1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A ≫ εA.1 := by
        show barPt A ≫ Spec.map (CommRingCat.ofHom M.ρ) ≫ M.ε₀.1 = _ ≫ barPt A ≫ Spec.map (CommRingCat.ofHom M.ρ) ≫ M.ε₀.1
        rw [hgen, ← Category.assoc, hσgen]
      have hεfix := ModularCurve.JZeroNeronObjectAtP.LevelModel.fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt N₀ p hpN₀ 𝔓 A hA M
        σ hσ εA εA hεconj
      have hεκ : curveFibrePt M εA = (sectionBaseChange (ResidueField ↥A) M.ε₀).1 := by
        apply pullback.hom_ext
        · rw [FROBDICT.curveFibrePt, pullback.lift_fst, sectionBaseChange, pullback.lift_fst]
          show Spec.map _ ≫ Spec.map _ ≫ M.ε₀.1 = Spec.map _ ≫ M.ε₀.1
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        · rw [FROBDICT.curveFibrePt, pullback.lift_snd, sectionBaseChange, pullback.lift_snd]
      rw [← hεκ, ← hφ]
      exact hεfix.symm
    rw [Category.id_comp, hε]
    apply pullback.hom_ext
    · rw [Category.assoc, FROBDICT.ajFibre, pullback.lift_fst, ← Category.assoc, sectionBaseChange,
        pullback.lift_fst, Category.assoc, M.haj₀ε, GoodReductionJacobian.RelativePic0Designation.baseChange_zeroSection_fst]
    · rw [Category.assoc, FROBDICT.ajFibre, pullback.lift_snd, ← Category.assoc, sectionBaseChange, pullback.lift_snd,
        (M.D₀.baseChange (ResidueField ↥A)).zeroSection_toBase, Category.id_comp]
  have hb : pt xb = (RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) hD₀κ).one (𝟙 _) :=
    Subtype.ext (hb1.trans (RepresentsRelSubPic.relativeGroupLaw_one
      (P := algEquivZeroGroupCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) hD₀κ).symm)
  rw [hb, RelativeGroupLaw.mul_one] at key

  apply Subtype.ext
  rw [FROBDICT.fibreMap_coe]
  have h1 : (ModularCurve.JZeroNeronObjectAtP.toFibrePt
      (castOver hseam (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl bA))).1 = curveFibrePt M xA ≫ ajFibre M := by
    rw [FROBDICT.toFibrePt_coe]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, FROBDICT.ajFibre, pullback.lift_fst, ← Category.assoc, FROBDICT.curveFibrePt,
        pullback.lift_fst, Category.assoc]
      rfl
    · rw [pullback.lift_snd, Category.assoc, FROBDICT.ajFibre, pullback.lift_snd, ← Category.assoc, FROBDICT.curveFibrePt,
        pullback.lift_snd, Category.id_comp]
  have h2 : resPt A ≫ zA.1 = curveFibrePt M zA ≫ pullback.fst _ _ := by
    rw [FROBDICT.curveFibrePt, pullback.lift_fst]
  have hR : (castOver hseam (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl cA)).1 = resPt A ≫ zA.1 ≫ M.aj₀.1 := rfl
  have hk' : (curveFibrePt M xA ≫ ajFibre M) ≫ F.1 = (curveFibrePt M xA ≫ φκ) ≫ ajFibre M := congrArg Subtype.val key
  rw [hR, h1, hk', ← Category.assoc (resPt A), h2, hz]
  simp only [Category.assoc, FROBDICT.ajFibre, pullback.lift_fst]

end S_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm (solution)
