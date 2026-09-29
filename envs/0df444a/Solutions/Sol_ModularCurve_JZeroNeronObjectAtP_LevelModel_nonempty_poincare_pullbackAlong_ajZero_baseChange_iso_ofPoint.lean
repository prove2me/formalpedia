-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/95b4577a-aad9-5fc3-80b2-2251e179d80d

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel IsLocalRing ModularCurve.JZeroNeronObjectAtP"

namespace AjbcKit

universe u

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

theorem nonempty_pullback_ker_invModule_iso_of_isIso {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X)
    [IsClosedImmersion p] (p' : T ⟶ Y) (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj p.ker.invModule ≅ p'.ker.invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj p.ker.module ≅ p'.ker.module) := by
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso f p p' hp hI hI' 1
  refine ⟨⟨?_ ≪≫ e₁ ≪≫ eqToIso (by rw [pow_one])⟩, ⟨?_ ≪≫ e₂ ≪≫ eqToIso (by rw [pow_one])⟩⟩
  · exact eqToIso (by rw [pow_one])
  · exact eqToIso (by rw [pow_one])

end AjbcKit

attribute [reassoc] AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst' AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_snd'
  AlgebraicGeometry.RelPicard.BaseChange.κ_hom_fst AlgebraicGeometry.RelPicard.BaseChange.κ_hom_snd

open AlgebraicGeometry.RelPicard.BaseChange in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    ∀ [IsSeparated (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀))
        (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))),
      Nonempty ((hD₀κ.poincare.pullbackAlong
          ⟨y.1 ≫ pullback.map (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)) M.D₀.toBase (specMap (R p) (ResidueField ↥A))
              M.aj₀.1 (𝟙 _) (𝟙 _) ((Category.comp_id _).trans M.aj₀.2.symm) ((Category.comp_id _).trans (Category.id_comp _).symm),
            (Category.assoc _ _ _).trans (((congrArg (y.1 ≫ ·) (pullback.lift_snd _ _ _)).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝟙 _) y.2).trans (Category.comp_id _)))))⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) y.1 y.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
            (𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 _ ≫ ·) (sectionBaseChange (ResidueField ↥A) M.ε₀).2).trans
              (Category.comp_id _)))).idealModule) := by
  letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
  intro _ hD₀κ hP₀κ y
  obtain ⟨eP₀⟩ := hP₀κ

  haveI : IsProper (toBase0 N₀ p) := M.proper₀
  let tκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (R p)) := 𝟙 _ ≫ specMap (R p) (ResidueField ↥A)
  let Φ := κ (toBase0 N₀ p) (ResidueField ↥A) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))

  have hΦfst := κ_hom_fst (toBase0 N₀ p) (ResidueField ↥A) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  have hΦsnd := κ_hom_snd (toBase0 N₀ p) (ResidueField ↥A) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))

  haveI : SmoothOfRelativeDimension 1 (toBase0 N₀ p) :=
    (ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral N₀ p hpN₀).2.1
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) := by
    dsimp only [SmoothProperCurve.baseChange]; infer_instance
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) :=
    inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ p) tκ) := inferInstance
  haveI : IsSeparated (pullback.snd (toBase0 N₀ p) tκ) := inferInstance
  haveI : IsSeparated (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) :=
    inferInstance

  have hx : (y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) ≫ toBase0 N₀ p = tκ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ specMap (R p) (ResidueField ↥A)) y.2
  obtain ⟨eAJ⟩ := M.haj₀ (ResidueField ↥A) tκ ⟨y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)), hx⟩

  have hgraphA : graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) y.1 y.2 ≫ Φ.hom =
      graphOver (toBase0 N₀ p) (y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) hx := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst, graphOver_fst_assoc]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]
  have hε : (tκ ≫ M.ε₀.1) ≫ toBase0 N₀ p = tκ :=
    (Category.assoc _ _ _).trans ((congrArg (tκ ≫ ·) M.ε₀.2).trans (Category.comp_id tκ))
  have hεκ : (𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1) ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (𝟙 _ ≫ ·) (sectionBaseChange (ResidueField ↥A) M.ε₀).2).trans (Category.comp_id _))
  have hgraphB : graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1) hεκ ≫ Φ.hom =
      graphOver (toBase0 N₀ p) (tκ ≫ M.ε₀.1) hε := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst, graphOver_fst_assoc, Category.assoc, sectionBaseChange_coe_fst]
      simp only [tκ, Category.assoc]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]

  have hIA := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase0 N₀ p) tκ)
    (graphOver (toBase0 N₀ p) (y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) hx) (graphOver_snd _ _ _)
  have hIA' := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))))
    (graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) y.1 y.2) (graphOver_snd _ _ _)
  have hIB := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase0 N₀ p) tκ)
    (graphOver (toBase0 N₀ p) (tκ ≫ M.ε₀.1) hε) (graphOver_snd _ _ _)
  have hIB' := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))))
    (graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _ ≫ (sectionBaseChange (ResidueField ↥A) M.ε₀).1) hεκ)
    (graphOver_snd _ _ _)
  obtain ⟨⟨jA⟩, -⟩ := AjbcKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
  obtain ⟨-, ⟨jB⟩⟩ := AjbcKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

  have hX : ((y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) ≫ M.aj₀.1) ≫ M.D₀.toBase = tκ :=
    (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) ≫ ·) M.aj₀.2).trans hx)
  have hcomp : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (M.D₀.baseChange (ResidueField ↥A)).toBase),
      P.1 = y.1 ≫ pullback.map (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)) M.D₀.toBase (specMap (R p) (ResidueField ↥A))
              M.aj₀.1 (𝟙 _) (𝟙 _) ((Category.comp_id _).trans M.aj₀.2.symm) ((Category.comp_id _).trans (Category.id_comp _).symm) →
      baseChangeSnd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) P ≫
          (κ (toBase0 N₀ p) (ResidueField ↥A) (M.D₀.baseChange (ResidueField ↥A)).toBase).hom ≫
          baseChangeSnd (toBase0 N₀ p) (⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩ :
            SchemeHomOver ((M.D₀.baseChange (ResidueField ↥A)).toBase ≫ specMap (R p) (ResidueField ↥A)) M.D₀.toBase) =
        Φ.hom ≫ baseChangeSnd (toBase0 N₀ p)
          (⟨(y.1 ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) ≫ M.aj₀.1, hX⟩ : SchemeHomOver tκ M.D₀.toBase) := by
    intro P hP
    apply pullback.hom_ext <;>
      simp only [Φ, Category.assoc, baseChangeSnd_fst', baseChangeSnd_snd', baseChangeSnd_fst'_assoc,
        baseChangeSnd_snd'_assoc, κ_hom_fst, κ_hom_snd_assoc, hP,
        pullback.lift_fst, RelativePic0Designation.baseChange_toBase]

  refine ⟨(Scheme.Modules.pullback _).mapIso eP₀ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _) ≪≫
    (Scheme.Modules.pullbackCongr (hcomp _ rfl)).app M.rep.poincare.L ≪≫
    ((Scheme.Modules.pullbackComp Φ.hom _).app _).symm ≪≫
    (Scheme.Modules.pullback Φ.hom).mapIso eAJ ≪≫
    Scheme.Modules.pullbackTensorObjIso Φ.hom _ _ ≪≫ (jA ⊗ᵢ jB)⟩

end S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_ajZero_baseChange_iso_ofPoint (solution)
