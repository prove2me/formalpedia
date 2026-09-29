-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/17ce977d-b435-5d9b-b6d6-e551317305a8

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
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points
import Theorems.Thm_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsFinite 𝔓.πw.1] [Flat 𝔓.πw.1] [LocallyOfFinitePresentation 𝔓.πw.1] (hrk_w : ∀ x, 𝔓.πw.1.finrank x = p + 1)

    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
      (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
    (hPκ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
    (hP₀κ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))

    (hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1)

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq₀ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0)
      hε₁' hDκ hD₀κ)
    (habq₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1)
            (𝔓.comp_over κ (algebraMap (R p) κ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

    (e : JZeroC κ N₀ ≃ SchemeHomOver (specMap (R p) κ) D₀.toBase)
    (he_add : ∀ u v : JZeroC κ N₀,
      e (u + v) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (e u) (e v))
    (he_frob : ∀ b : SchemeHomOver (specMap (R p) κ) D₀.toBase,
      e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap F b) = frobeniusPushforwardModL κ N₀ p (e.symm b)) :

    ∀ x : SchemeHomOver (specMap (R p) κ) D.toBase,
      e.symm (NeronModelInfra.schemeHomOverComp x (δ 0)) =
          e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 0) x) +
            frobeniusPushforwardModL κ N₀ p (e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 1) x)) ∧
      e.symm (NeronModelInfra.schemeHomOverComp x (δ 1)) =
          frobeniusPushforwardModL κ N₀ p (e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 0) x)) +
            e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq 1) x) := by
  classical
  intro x

  let L₀ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase0 N₀ p) ε₀) hD₀

  have htb : ∀ {X : Scheme.{0}} {g : X ⟶ Spec (CommRingCat.of (R p))} (y : SchemeHomOver (specMap (R p) κ) g),
      RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) (ModularCurve.JZeroNeronObjectAtP.toFibrePt y) =
        ModularCurve.JZeroNeronObjectAtP.overId y :=
    fun y => RelativeGroupLaw.baseChangePointToBase_ofBase (specMap (R p) κ) _
  have htoF : ∀ (φ : SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase),
      NeronModelInfra.schemeHomOverComp (ModularCurve.JZeroNeronObjectAtP.toFibrePt x) φ =
        ModularCurve.JZeroNeronObjectAtP.toFibrePt (ModularCurve.JZeroNeronObjectAtP.fibreMap φ x) :=
    fun φ => (RelativeGroupLaw.baseChangePointOfBase_toBase (specMap (R p) κ) _).symm
  have htoFF : ∀ (y : SchemeHomOver (specMap (R p) κ) D₀.toBase),
      NeronModelInfra.schemeHomOverComp (ModularCurve.JZeroNeronObjectAtP.toFibrePt y) F =
        ModularCurve.JZeroNeronObjectAtP.toFibrePt (ModularCurve.JZeroNeronObjectAtP.fibreMap F y) :=
    fun y => (RelativeGroupLaw.baseChangePointOfBase_toBase (specMap (R p) κ) _).symm
  have hcompover : ∀ i : Fin 2,
      NeronModelInfra.schemeHomOverComp (ModularCurve.JZeroNeronObjectAtP.overId x) (δ i) =
        ModularCurve.JZeroNeronObjectAtP.overId (NeronModelInfra.schemeHomOverComp x (δ i)) :=
    fun i => Subtype.ext rfl

  have hlaw : ∀ u v : SchemeHomOver (specMap (R p) κ) D₀.toBase,
      ModularCurve.JZeroNeronObjectAtP.overId (L₀.mul (specMap (R p) κ) u v) =
        L₀.mul (𝟙 _ ≫ (specMap (R p) κ)) (ModularCurve.JZeroNeronObjectAtP.overId u) (ModularCurve.JZeroNeronObjectAtP.overId v) := by
    intro u v
    have hid : ∀ w : SchemeHomOver (specMap (R p) κ) D₀.toBase,
        GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl w = ModularCurve.JZeroNeronObjectAtP.overId w :=
      fun w => Subtype.ext (Category.id_comp _)
    rw [← hid, ← hid, ← hid, L₀.mul_natural]
  have hinj : ∀ u v : SchemeHomOver (specMap (R p) κ) D₀.toBase,
      ModularCurve.JZeroNeronObjectAtP.overId u = ModularCurve.JZeroNeronObjectAtP.overId v → u = v :=
    fun u v h => Subtype.ext (congrArg Subtype.val h)

  have habq : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq i))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) t)).obj
            (hDκ.poincare.pullbackAlong a).L)) :=
    Fin.forall_fin_two.mpr
      ⟨fun {T} t a => by
          rw [habq₀]
          exact RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
            (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0) hε₁' hDκ hD₀κ t a,
        fun {T} t a => habq₁ t a⟩

  obtain ⟨h0, h1⟩ :=
    ModularCurve.DRModelPackageLevel.baseChange_normHom_eq_restrict_mul_frob_restrict_points N₀ p hpN₀ 𝔓 hrk D hD ε₀ D₀ hD₀
      hrk_w δ hδ₀ hδ₁ κ hDκ hPκ hD₀κ hP₀κ abq habq φκ hφκ hφκ_over hφ_rk F hF (ModularCurve.JZeroNeronObjectAtP.toFibrePt x)

  have hL := AlgebraicGeometry.RelPicard.relativeGroupLaw_baseChange_eq (R p) (toBase0 N₀ p) ε₀ D₀ hD₀ κ hD₀κ hP₀κ
  rw [hL, RelativeGroupLaw.baseChange_mul] at h0 h1
  replace h0 := congrArg (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ)) h0
  replace h1 := congrArg (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ)) h1
  simp only [RelativeGroupLaw.baseChangePointToBase_ofBase, htb, htoF, htoFF, hcompover] at h0 h1
  rw [← hlaw] at h0 h1
  have k0 := hinj _ _ h0
  have k1 := hinj _ _ h1

  have hsplit : ∀ u v : SchemeHomOver (specMap (R p) κ) D₀.toBase, e.symm (L₀.mul (specMap (R p) κ) u v) = e.symm u + e.symm v := by
    intro u v
    apply e.injective
    rw [he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · rw [k0, hsplit, he_frob]
  · rw [k1, hsplit, he_frob]

end S_ModularCurve_DRModelPackageLevel_symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_symm_schemeHomOverComp_degeneracyHom_eq_add_frobeniusPushforwardModL_of_dictionary (solution)
