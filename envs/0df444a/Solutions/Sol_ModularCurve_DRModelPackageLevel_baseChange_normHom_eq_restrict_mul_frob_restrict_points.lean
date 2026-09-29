-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.baseChange_normHom_eq_restrict_mul_frob_restrict_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9041f116-56fa-5301-9199-1d3621804fb0

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
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_one_iso_id
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel"

namespace CLASSIFY

universe u

section reassoc
variable {R : Type u} [CommRing R]

private theorem κ_hom_snd_assoc {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (R' : Type u) [CommRing R']
    [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) {Z : Scheme.{u}} (h : T ⟶ Z) :
    (BaseChange.κ c R' t').hom ≫ pullback.snd c (t' ≫ specMap R R') ≫ h = pullback.snd (baseChange R c R') t' ≫ h := by
  rw [← Category.assoc, BaseChange.κ_hom_snd]

private theorem baseChangeSnd_fst'_assoc {C T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) {Z : Scheme.{u}}
    (h : C ⟶ Z) : baseChangeSnd cc ψ ≫ pullback.fst cc t ≫ h = pullback.fst cc t' ≫ h := by
  rw [← Category.assoc, BaseChange.baseChangeSnd_fst']

private theorem baseChangeSnd_snd'_assoc {C T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) {Z : Scheme.{u}}
    (h : T ⟶ Z) : baseChangeSnd cc ψ ≫ pullback.snd cc t ≫ h = (pullback.snd cc t' ≫ ψ.1) ≫ h := by
  rw [← Category.assoc, BaseChange.baseChangeSnd_snd']

end reassoc

theorem nonempty_rigidify_iso_of_field {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k)) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) : Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback σ).dual.1
  exact ⟨(Iso.refl L ⊗ᵢ ((Scheme.Modules.pullback q).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso q)) ≪≫ ρ_ L⟩

variable {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K]

theorem rigSection_comp_fst {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection (baseChange R c K) (𝟙 _) (sectionBaseChange K ε) ≫ pullback.fst (baseChange R c K) (𝟙 _) =
      𝟙 _ ≫ rigSection c (specMap R K) ε := by
  apply pullback.hom_ext
  · simp only [Category.id_comp, BaseChange.rigSection_fst', sectionBaseChange_coe_fst]
  · have h := pullback.condition (f := baseChange R c K) (g := 𝟙 (Spec (CommRingCat.of K)))
    simp only [Category.assoc, Category.id_comp, Category.comp_id, BaseChange.rigSection_snd'] at h ⊢
    rw [h, BaseChange.rigSection_snd']

theorem fst_comp_snd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback.fst (baseChange R c K) (𝟙 _) ≫ pullback.snd c (specMap R K) =
      pullback.snd (baseChange R c K) (𝟙 (Spec (CommRingCat.of K))) ≫ 𝟙 _ :=
  pullback.condition

theorem fst_comp_eq_curveChange_comp_fst {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of R))
    (c₂ : C₂ ⟶ Spec (CommRingCat.of R))
    (φ : pullback c₁ (specMap R K) ⟶ pullback c₂ (specMap R K)) (hφ : φ ≫ baseChange R c₂ K = baseChange R c₁ K) :
    pullback.fst (baseChange R c₁ K) (𝟙 _) ≫ φ =
      curveChange φ hφ (𝟙 (Spec (CommRingCat.of K))) ≫ pullback.fst (baseChange R c₂ K) (𝟙 _) := by
  simp only [RelPicard.curveChange, pullback.map, pullback.lift_fst]

theorem baseChangeSnd_κ_hom_baseChangeSnd {C D : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (d : D ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (pullback.snd d (specMap R K)))
    (x₀ : SchemeHomOver (specMap R K) d) (hx₀ : x₀.1 = x.1 ≫ pullback.fst d (specMap R K)) :
    (baseChangeSnd (baseChange R c K) x ≫ (BaseChange.κ c K (pullback.snd d (specMap R K))).hom) ≫
        baseChangeSnd c (⟨pullback.fst d (specMap R K), pullback.condition⟩ :
          SchemeHomOver (pullback.snd d (specMap R K) ≫ specMap R K) d) =
      pullback.fst (baseChange R c K) (𝟙 _) ≫ baseChangeSnd c x₀ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, baseChangeSnd_fst'_assoc]
  · simp only [Category.assoc, BaseChange.baseChangeSnd_snd', κ_hom_snd_assoc, baseChangeSnd_snd'_assoc, hx₀]
    rw [← Category.assoc (pullback.fst _ _), fst_comp_snd, Category.assoc, Category.id_comp]

end CLASSIFY

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

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq i))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) t)).obj
            (hDκ.poincare.pullbackAlong a).L)))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L))) :
    ∀ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (D.baseChange κ).toBase,
      RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0)) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp a (abq 0))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 1)) F) ∧
      RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1)) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 0)) F)
          (NeronModelInfra.schemeHomOverComp a (abq 1)) := by
  intro a

  let t : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (R p)) := specMap (R p) κ
  let a' : SchemeHomOver (𝟙 _ ≫ t) D.toBase := RelativeGroupLaw.baseChangePointToBase t a
  let a₀ : SchemeHomOver t D.toBase := ⟨a'.1, by rw [a'.2, Category.id_comp]⟩
  have ha₀ : a₀.1 = a'.1 := rfl

  let L := (hD.poincare.pullbackAlong a₀).L

  have S1 := hδ₀ t a₀

  haveI : IsIntegral (fibre0 (N₀ := N₀) (algebraMap (R p) κ)) := ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charP N₀ p hpN₀ κ

  have sq : IsPullback (pullback.fst (toBase N₀ p) t) (curveChange 𝔓.π.1 𝔓.π.2 t) 𝔓.π.1
      (pullback.fst (toBase0 N₀ p) t) := by
    have s0 : IsPullback (pullback.fst (toBase N₀ p) t) (pullback.snd (toBase N₀ p) t) (toBase N₀ p) t :=
      IsPullback.of_hasPullback _ _
    have s : IsPullback (pullback.fst (toBase N₀ p) t)
        (curveChange 𝔓.π.1 𝔓.π.2 t ≫ pullback.snd (toBase0 N₀ p) t) (𝔓.π.1 ≫ toBase0 N₀ p) t := by
      rw [RelPicard.curveChange_snd, 𝔓.π.2]; exact s0
    exact IsPullback.of_bot s (by simp only [RelPicard.curveChange, pullback.map, pullback.lift_fst])
      (IsPullback.of_hasPullback (toBase0 N₀ p) t)
  haveI : IsFinite (curveChange 𝔓.π.1 𝔓.π.2 t) := MorphismProperty.of_isPullback sq inferInstance
  haveI : Flat (curveChange 𝔓.π.1 𝔓.π.2 t) := MorphismProperty.of_isPullback sq inferInstance
  haveI : LocallyOfFinitePresentation (curveChange 𝔓.π.1 𝔓.π.2 t) :=
    MorphismProperty.of_isPullback sq inferInstance
  have hrkκ : ∀ x, (curveChange 𝔓.π.1 𝔓.π.2 t).finrank x = p + 1 := fun x => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq x]; exact hrk _
  haveI : IsClosedImmersion (𝔓.comp κ (algebraMap (R p) κ) 0) := 𝔓.comp_isClosedImmersion κ _ 0
  haveI : IsClosedImmersion (𝔓.comp κ (algebraMap (R p) κ) 1) := 𝔓.comp_isClosedImmersion κ _ 1
  have h0 : 𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t = 𝟙 _ := 𝔓.comp_pi κ _
  have h1 : 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.π.1 𝔓.π.2 t = φκ := hφκ.symm
  haveI : IsFinite (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by rw [h0]; infer_instance
  haveI : Flat (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by rw [h0]; infer_instance
  haveI : LocallyOfFinitePresentation (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by
    rw [h0]; infer_instance
  haveI : IsFinite (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by rw [h1]; infer_instance
  haveI : Flat (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by rw [h1]; infer_instance
  haveI : LocallyOfFinitePresentation (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) := by
    rw [h1]; infer_instance
  have hd₀ : ∀ x, (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t).finrank x = 1 := by
    intro x; rw [h0]
    exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso (𝟙 _)) x
  have hd₁ : ∀ x, (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.π.1 𝔓.π.2 t).finrank x = p := by
    intro x; rw [h1]; exact hφ_rk x
  have hcovκ : ∀ (U : (fibre (N₀ := N₀) (algebraMap (R p) κ)).Opens) (s : Γ(fibre (N₀ := N₀) (algebraMap (R p) κ), U)),
      ((𝔓.comp κ (algebraMap (R p) κ) 0).app U).hom s = 0 → ((𝔓.comp κ (algebraMap (R p) κ) 1).app U).hom s = 0 →
        s = 0 := by
    haveI : IsReduced (fibre (N₀ := N₀) (algebraMap (R p) κ)) := 𝔓.fibre_reduced κ _
    have hcover : Set.range (𝔓.comp κ (algebraMap (R p) κ) 0).base ∪
        Set.range (𝔓.comp κ (algebraMap (R p) κ) 1).base = Set.univ :=
      Set.eq_univ_of_forall fun y => 𝔓.comp_jointly_surjective κ _ y
    intro U s hs0 hs1
    have hinj := (AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced
      (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1) hcover U).1
    apply hinj
    change (((𝔓.comp κ (algebraMap (R p) κ) 0).app U).hom s, ((𝔓.comp κ (algebraMap (R p) κ) 1).app U).hom s) =
      (((𝔓.comp κ (algebraMap (R p) κ) 0).app U).hom 0, ((𝔓.comp κ (algebraMap (R p) κ) 1).app U).hom 0)
    rw [hs0, hs1, map_zero, map_zero]
  have hL : Scheme.Modules.IsInvertible L := (hD.poincare.pullbackAlong a₀).isInvertible
  obtain ⟨eN⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
    (curveChange 𝔓.π.1 𝔓.π.2 t) (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)
    (p + 1) 1 p hrkκ hd₀ hd₁ (by omega) hcovκ hL

  have S3 : Nonempty (Scheme.Modules.normModule (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.π.1 𝔓.π.2 t) 1
      ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L) ≅
      (Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L) := by
    obtain ⟨e1⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_one_iso_id (fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    set M := (Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L
    refine ⟨Scheme.Modules.normModuleCongr h0 1 M ≪≫ Scheme.Modules.normModuleIdIso 1 M ≪≫ ?_ ≪≫ ρ_ M⟩
    exact e1.app M ⊗ᵢ (Scheme.Modules.dualCongr (e1.app (𝟙_ _)) ≪≫ MonoidalClosed.unitIsoSelf (𝟙_ _))

  haveI heYiso : IsIso (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 (Spec (CommRingCat.of κ)))) := inferInstance
  have Eσ := CLASSIFY.rigSection_comp_fst (K := κ) (toBase0 N₀ p) ε₀
  have Eq := CLASSIFY.fst_comp_snd (K := κ) (toBase0 N₀ p)

  have Eφ := CLASSIFY.fst_comp_eq_curveChange_comp_fst (toBase0 N₀ p) (toBase0 N₀ p) φκ hφκ_over
  have sqφ : IsPullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) (curveChange φκ hφκ_over (𝟙 _)) φκ
      (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) := IsPullback.of_horiz_isIso ⟨Eφ⟩
  haveI : IsFinite (curveChange φκ hφκ_over (𝟙 _)) := MorphismProperty.of_isPullback sqφ inferInstance
  haveI : Flat (curveChange φκ hφκ_over (𝟙 _)) := MorphismProperty.of_isPullback sqφ inferInstance
  haveI : LocallyOfFinitePresentation (curveChange φκ hφκ_over (𝟙 _)) := MorphismProperty.of_isPullback sqφ inferInstance
  have hφ'_rk : ∀ x, (curveChange φκ hφκ_over (𝟙 _)).finrank x = p := fun x => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqφ x]; exact hφ_rk _

  have E1 := CLASSIFY.baseChangeSnd_κ_hom_baseChangeSnd (K := κ) (toBase0 N₀ p) D₀.toBase
    (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
      (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0)))
    (NeronModelInfra.schemeHomOverComp a₀ (δ 0))
    (by rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; rfl)

  have E2 := fun i : Fin 2 => CLASSIFY.baseChangeSnd_κ_hom_baseChangeSnd (K := κ) (toBase N₀ p) D.toBase a a₀ ha₀
  have E3 := fun i : Fin 2 => CLASSIFY.fst_comp_eq_curveChange_comp_fst (toBase0 N₀ p) (toBase N₀ p)
    (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i)

  have E23 : ∀ i : Fin 2,
      curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) (𝟙 _) ≫
          baseChangeSnd (baseChange (R p) (toBase N₀ p) κ) a ≫
            (BaseChange.κ (toBase N₀ p) κ (D.baseChange κ).toBase).hom ≫
              baseChangeSnd (toBase N₀ p) (⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩ :
                SchemeHomOver ((D.baseChange κ).toBase ≫ specMap (R p) κ) D.toBase) =
        pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) ≫ 𝔓.comp κ (algebraMap (R p) κ) i ≫
          baseChangeSnd (toBase N₀ p) a₀ := by
    intro i
    rw [← Category.assoc (pullback.fst _ _), E3 i, Category.assoc, ← E2 i]
    simp only [Category.assoc]
  have E1' : baseChangeSnd (baseChange (R p) (toBase0 N₀ p) κ)
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0))) ≫
        (BaseChange.κ (toBase0 N₀ p) κ (D₀.baseChange κ).toBase).hom ≫
          baseChangeSnd (toBase0 N₀ p) (⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩ :
            SchemeHomOver ((D₀.baseChange κ).toBase ≫ specMap (R p) κ) D₀.toBase) =
      pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) ≫
        baseChangeSnd (toBase0 N₀ p) (NeronModelInfra.schemeHomOverComp a₀ (δ 0)) := by
    simpa only [Category.assoc] using E1

  have IM : ∀ i : Fin 2, Nonempty
      ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) (𝟙 _))).obj
          (hDκ.poincare.pullbackAlong a).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
          ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) i)).obj L)) := fun i =>
    ⟨(Scheme.Modules.pullback _).mapIso
        ((Scheme.Modules.pullback (baseChangeSnd (baseChange (R p) (toBase N₀ p) κ) a)).mapIso hPκ.some) ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso
        ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L)) ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hD.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr (E23 i)).app hD.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L).symm ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L).symm⟩

  have Ilhs : Nonempty
      ((hD₀κ.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0)))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
          (hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a₀ (δ 0))).L) :=
    ⟨(Scheme.Modules.pullback _).mapIso hP₀κ.some ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr E1').app hD₀.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L).symm⟩

  have hInv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L ⊗
        Scheme.Modules.normModule φκ p ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L)) :=
    (hL.pullback _).tensor (AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule φκ p hφ_rk (hL.pullback _))

  have LHS1 : Nonempty
      ((hD₀κ.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 0)))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
            ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L) ⊗
          Scheme.Modules.normModule (curveChange φκ hφκ_over (𝟙 _)) p
            ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
              ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L))) := by
    obtain ⟨i1⟩ := Ilhs
    obtain ⟨i2⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
      (σ := rigSection (toBase0 N₀ p) t ε₀) (q := pullback.snd (toBase0 N₀ p) t)
      (σ' := rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (q' := pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (𝟙 _) (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) Eσ Eq hInv
    obtain ⟨i3⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (hInv.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)))
    obtain ⟨i4⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso φκ p hφ_rk
      (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) (curveChange φκ hφκ_over (𝟙 _))
      (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) sqφ (hL.pullback (𝔓.comp κ (algebraMap (R p) κ) 1))
    exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso (S1.some ≪≫ Scheme.Modules.rigidifyMapIso _ _
        (eN ≪≫ (S3.some ⊗ᵢ Scheme.Modules.normModuleCongr h1 p _))) ≪≫ i2 ≪≫ i3 ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ i4)⟩

  have RHS1 : Nonempty
      ((hD₀κ.poincare.pullbackAlong
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp a (abq 0))
            (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 1)) F))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
            ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L) ⊗
          Scheme.Modules.normModule (curveChange φκ hφκ_over (𝟙 _)) p
            ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
              ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L))) := by
    obtain ⟨m⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso
      (P := algEquivZeroGroupCut _ _) hD₀κ (𝟙 _) (NeronModelInfra.schemeHomOverComp a (abq 0))
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 1)) F)
    obtain ⟨b0⟩ := habq 0 (𝟙 _) a
    obtain ⟨b1⟩ := habq 1 (𝟙 _) a
    obtain ⟨f1⟩ := hF (𝟙 _) (NeronModelInfra.schemeHomOverComp a (abq 1))
    obtain ⟨r0⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      ((hDκ.poincare.pullbackAlong a).isInvertible.pullback
        (curveChange (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0) (𝟙 _)))
    obtain ⟨r1⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      ((hDκ.poincare.pullbackAlong a).isInvertible.pullback
        (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1) (𝔓.comp_over κ (algebraMap (R p) κ) 1) (𝟙 _)))
    obtain ⟨rN⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule (curveChange φκ hφκ_over (𝟙 _)) p hφ'_rk
        (hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).isInvertible)
    obtain ⟨j0⟩ := IM 0
    obtain ⟨j1⟩ := IM 1
    exact ⟨m ≪≫ ((b0 ≪≫ r0 ≪≫ j0) ⊗ᵢ (f1 ≪≫ rN ≪≫ Scheme.Modules.normModuleMapIso _ p (b1 ≪≫ r1 ≪≫ j1)))⟩

  have S1w := hδ₁ t a₀
  have sqw : IsPullback (pullback.fst (toBase N₀ p) t) (curveChange 𝔓.πw.1 𝔓.πw.2 t) 𝔓.πw.1
      (pullback.fst (toBase0 N₀ p) t) := by
    have s0 : IsPullback (pullback.fst (toBase N₀ p) t) (pullback.snd (toBase N₀ p) t) (toBase N₀ p) t :=
      IsPullback.of_hasPullback _ _
    have s : IsPullback (pullback.fst (toBase N₀ p) t)
        (curveChange 𝔓.πw.1 𝔓.πw.2 t ≫ pullback.snd (toBase0 N₀ p) t) (𝔓.πw.1 ≫ toBase0 N₀ p) t := by
      rw [RelPicard.curveChange_snd, 𝔓.πw.2]; exact s0
    exact IsPullback.of_bot s (by simp only [RelPicard.curveChange, pullback.map, pullback.lift_fst])
      (IsPullback.of_hasPullback (toBase0 N₀ p) t)
  haveI : IsFinite (curveChange 𝔓.πw.1 𝔓.πw.2 t) := MorphismProperty.of_isPullback sqw inferInstance
  haveI : Flat (curveChange 𝔓.πw.1 𝔓.πw.2 t) := MorphismProperty.of_isPullback sqw inferInstance
  haveI : LocallyOfFinitePresentation (curveChange 𝔓.πw.1 𝔓.πw.2 t) :=
    MorphismProperty.of_isPullback sqw inferInstance
  have hrkκw : ∀ x, (curveChange 𝔓.πw.1 𝔓.πw.2 t).finrank x = p + 1 := fun x => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqw x]; exact hrk_w _

  have hw : curveChange 𝔓.πw.1 𝔓.πw.2 t =
      fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ curveChange 𝔓.π.1 𝔓.π.2 t := by
    apply pullback.hom_ext <;>
      simp +zetaDelta only [RelPicard.curveChange, fibreMap, pullback.map, DRModelPackageLevel.πw_val, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, Category.comp_id]
  have hww : fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [fibreMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      rw [𝔓.w_invol, Category.comp_id]
    · simp only [fibreMap, pullback.map, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
  have h0w : 𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t = φκ := by
    rw [hw, ← Category.assoc, 𝔓.comp_w, h1]
  have h1w : 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t = 𝟙 _ := by
    rw [hw, ← Category.assoc, ← 𝔓.comp_w κ (algebraMap (R p) κ), Category.assoc (𝔓.comp κ _ 0), hww,
      Category.comp_id, h0]
  haveI : IsFinite (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by rw [h1w]; infer_instance
  haveI : Flat (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by rw [h1w]; infer_instance
  haveI : LocallyOfFinitePresentation (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by
    rw [h1w]; infer_instance
  haveI : IsFinite (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by rw [h0w]; infer_instance
  haveI : Flat (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by rw [h0w]; infer_instance
  haveI : LocallyOfFinitePresentation (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) := by
    rw [h0w]; infer_instance
  have hd₀w : ∀ x, (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t).finrank x = 1 := by
    intro x; rw [h1w]
    exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso (𝟙 _)) x
  have hd₁w : ∀ x, (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t).finrank x = p := by
    intro x; rw [h0w]; exact hφ_rk x
  obtain ⟨eNw⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
    (curveChange 𝔓.πw.1 𝔓.πw.2 t) (𝔓.comp κ (algebraMap (R p) κ) 1) (𝔓.comp κ (algebraMap (R p) κ) 0)
    (p + 1) 1 p hrkκw hd₀w hd₁w (by omega) (fun U s hs1 hs0 => hcovκ U s hs0 hs1) hL
  have S3w : Nonempty (Scheme.Modules.normModule (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ curveChange 𝔓.πw.1 𝔓.πw.2 t) 1
      ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L) ≅
      (Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L) := by
    obtain ⟨e1⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_one_iso_id (fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    set M := (Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L
    refine ⟨Scheme.Modules.normModuleCongr h1w 1 M ≪≫ Scheme.Modules.normModuleIdIso 1 M ≪≫ ?_ ≪≫ ρ_ M⟩
    exact e1.app M ⊗ᵢ (Scheme.Modules.dualCongr (e1.app (𝟙_ _)) ≪≫ MonoidalClosed.unitIsoSelf (𝟙_ _))
  have hInvw : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L ⊗
        Scheme.Modules.normModule φκ p ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L)) :=
    (hL.pullback _).tensor (AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule φκ p hφ_rk (hL.pullback _))
  have E1w := CLASSIFY.baseChangeSnd_κ_hom_baseChangeSnd (K := κ) (toBase0 N₀ p) D₀.toBase
    (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
      (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1)))
    (NeronModelInfra.schemeHomOverComp a₀ (δ 1))
    (by rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; rfl)
  have E1w' : baseChangeSnd (baseChange (R p) (toBase0 N₀ p) κ)
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1))) ≫
        (BaseChange.κ (toBase0 N₀ p) κ (D₀.baseChange κ).toBase).hom ≫
          baseChangeSnd (toBase0 N₀ p) (⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩ :
            SchemeHomOver ((D₀.baseChange κ).toBase ≫ specMap (R p) κ) D₀.toBase) =
      pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) ≫
        baseChangeSnd (toBase0 N₀ p) (NeronModelInfra.schemeHomOverComp a₀ (δ 1)) := by
    simpa only [Category.assoc] using E1w
  have Ilhsw : Nonempty
      ((hD₀κ.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1)))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
          (hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a₀ (δ 1))).L) :=
    ⟨(Scheme.Modules.pullback _).mapIso hP₀κ.some ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr E1w').app hD₀.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hD₀.poincare.L).symm⟩
  have LHS2 : Nonempty
      ((hD₀κ.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) κ)
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specMap (R p) κ) a) (δ 1)))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
            ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L) ⊗
          Scheme.Modules.normModule (curveChange φκ hφκ_over (𝟙 _)) p
            ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
              ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L))) := by
    obtain ⟨i1⟩ := Ilhsw
    obtain ⟨i2⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
      (σ := rigSection (toBase0 N₀ p) t ε₀) (q := pullback.snd (toBase0 N₀ p) t)
      (σ' := rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (q' := pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (𝟙 _) (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) Eσ Eq hInvw
    obtain ⟨i3⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (hInvw.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)))
    obtain ⟨i4⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso φκ p hφ_rk
      (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) (curveChange φκ hφκ_over (𝟙 _))
      (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _)) sqφ (hL.pullback (𝔓.comp κ (algebraMap (R p) κ) 0))
    obtain ⟨s3⟩ := S3w
    exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso (S1w.some ≪≫ Scheme.Modules.rigidifyMapIso _ _
        (eNw ≪≫ (s3 ⊗ᵢ Scheme.Modules.normModuleCongr h0w p _))) ≪≫ i2 ≪≫ i3 ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ i4)⟩
  have RHS2 : Nonempty
      ((hD₀κ.poincare.pullbackAlong
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 0)) F)
            (NeronModelInfra.schemeHomOverComp a (abq 1)))).L ≅
        (Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
            ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 1)).obj L) ⊗
          Scheme.Modules.normModule (curveChange φκ hφκ_over (𝟙 _)) p
            ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))).obj
              ((Scheme.Modules.pullback (𝔓.comp κ (algebraMap (R p) κ) 0)).obj L))) := by
    obtain ⟨m⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso
      (P := algEquivZeroGroupCut _ _) hD₀κ (𝟙 _)
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a (abq 0)) F)
      (NeronModelInfra.schemeHomOverComp a (abq 1))
    obtain ⟨b0⟩ := habq 0 (𝟙 _) a
    obtain ⟨b1⟩ := habq 1 (𝟙 _) a
    obtain ⟨f0⟩ := hF (𝟙 _) (NeronModelInfra.schemeHomOverComp a (abq 0))
    obtain ⟨r0⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      ((hDκ.poincare.pullbackAlong a).isInvertible.pullback
        (curveChange (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0) (𝟙 _)))
    obtain ⟨r1⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      ((hDκ.poincare.pullbackAlong a).isInvertible.pullback
        (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1) (𝔓.comp_over κ (algebraMap (R p) κ) 1) (𝟙 _)))
    obtain ⟨rN⟩ := CLASSIFY.nonempty_rigidify_iso_of_field
      (rigSection (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _) (sectionBaseChange κ ε₀))
      (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) (𝟙 _))
      (AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule (curveChange φκ hφκ_over (𝟙 _)) p hφ'_rk
        (hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 0))).isInvertible)
    obtain ⟨j0⟩ := IM 0
    obtain ⟨j1⟩ := IM 1
    exact ⟨m ≪≫ ((f0 ≪≫ rN ≪≫ Scheme.Modules.normModuleMapIso _ p (b0 ≪≫ r0 ≪≫ j0)) ⊗ᵢ (b1 ≪≫ r1 ≪≫ j1)) ≪≫ β_ _ _⟩
  exact ⟨RepresentsRelSubPic.ext_of_iso hD₀κ (𝟙 _) _ _ ⟨LHS1.some ≪≫ RHS1.some.symm⟩,
    RepresentsRelSubPic.ext_of_iso hD₀κ (𝟙 _) _ _ ⟨LHS2.some ≪≫ RHS2.some.symm⟩⟩

end S_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points (solution)
