-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/292a650e-e985-52ec-bd9e-054170efbf76

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
import Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre
import Theorems.Thm_ModularCurve_DRModelPackageLevel_baseChange_normHom_eq_restrict_mul_frob_restrict_points
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback
import Theorems.Thm_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp
import Theorems.Thm_ModularCurve_DRModelPackageLevel_schemeHomOverComp_frob_eq_of_dualNumber
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_comp_one_pi
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_residue
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyIntegral_igusaTo
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange
import Theorems.Thm_ModularCurve_DRModelPackageLevel_fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix
import Theorems.Thm_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelPicard.RigKerDualNumber.setoid kmfloorsGlue_int_three_isPrime"
p2m_attr_erase "instance" "kmfloorsGlue_int_bot_isPrime ValuationSubring.instIsAlgClosedResidueField AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma RegularLocalRingQuotientAscent.dualNumberFst_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 ValuationSubring.reduceAt_coe"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf"
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

universe u

namespace KerRed56c2139d

theorem nonempty_iso {X B S : Scheme.{u}} (sB : B ⟶ S) (u : X ⟶ pullback sB sB) (e : S ⟶ B)
    (he : e ≫ sB = 𝟙 S) :
    Nonempty (pullback (pullback.fst (u ≫ pullback.fst sB sB) e) (pullback.fst (u ≫ pullback.snd sB sB) e) ≅
      pullback u (pullback.lift e e rfl : S ⟶ pullback sB sB)) := by

  set d₀ := u ≫ pullback.fst sB sB with hd₀
  set d₁ := u ≫ pullback.snd sB sB with hd₁

  have c0 : pullback.fst d₀ e ≫ u ≫ pullback.fst sB sB = pullback.snd d₀ e ≫ e := pullback.condition
  have c1 : pullback.fst d₁ e ≫ u ≫ pullback.snd sB sB = pullback.snd d₁ e ≫ e := pullback.condition
  have cout : pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.fst d₀ e = pullback.snd (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.fst d₁ e := pullback.condition

  have hS : pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.snd d₀ e = pullback.snd (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.snd d₁ e := by
    have h0 : pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.snd d₀ e = pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.fst d₀ e ≫ u ≫ pullback.fst sB sB ≫ sB := by
      conv_lhs => rw [← Category.comp_id (pullback.snd d₀ e), ← he, ← Category.assoc (pullback.snd d₀ e), ← c0]
      simp only [Category.assoc]
    have h1 : pullback.snd (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.snd d₁ e = pullback.snd (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.fst d₁ e ≫ u ≫ pullback.snd sB sB ≫ sB := by
      conv_lhs => rw [← Category.comp_id (pullback.snd d₁ e), ← he, ← Category.assoc (pullback.snd d₁ e), ← c1]
      simp only [Category.assoc]
    rw [h0, h1, ← pullback.condition (f := sB) (g := sB), ← Category.assoc (pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e)), cout, Category.assoc]
  refine ⟨⟨pullback.lift (pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.fst d₀ e) (pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e) ≫ pullback.snd d₀ e) ?_,
    pullback.lift
      (pullback.lift (pullback.fst u _) (pullback.snd u _) ?_)
      (pullback.lift (pullback.fst u _) (pullback.snd u _) ?_) ?_, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [c0]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc (pullback.fst (pullback.fst d₀ e) (pullback.fst d₁ e)) (pullback.snd d₀ e), hS, Category.assoc,
        ← c1, ← Category.assoc (pullback.snd (pullback.fst d₀ e) (pullback.fst d₁ e)), ← cout, Category.assoc]
  · have := pullback.condition (f := u) (g := (pullback.lift e e rfl : S ⟶ pullback sB sB))
    rw [hd₀, ← Category.assoc, this, Category.assoc, pullback.lift_fst]
  · have := pullback.condition (f := u) (g := (pullback.lift e e rfl : S ⟶ pullback sB sB))
    rw [hd₁, ← Category.assoc, this, Category.assoc, pullback.lift_snd]
  · rw [pullback.lift_fst, pullback.lift_fst]
  · apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]
    · exact cout
    · exact hS
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

end KerRed56c2139d

open ModularCurve ModularCurve.DRLevel

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

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

    (hcusp : 𝔓.εinf.1 ≫ 𝔓.π.1 = ε₀.1)

    (hsm : Smooth D.toBase) (hsm₀ : Smooth D₀.toBase) (hpr₀ : IsProper D₀.toBase)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (c : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (R p))) :
    IsReduced
      (pullback
        (pullback.fst (NeronSpecialFibreInfra.fibreRestrictAlong c D₀.toBase D.toBase (δ 0)).1
          (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange c).one (𝟙 _)).1)
        (pullback.fst (NeronSpecialFibreInfra.fibreRestrictAlong c D₀.toBase D.toBase (δ 1)).1
          (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange c).one (𝟙 _)).1)) := by
  classical

  obtain ⟨toκ, rfl⟩ : ∃ φ : R p →+* κ, c = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage c).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  letI : Algebra (R p) κ := toκ.toAlgebra
  have hspec : specMap (R p) κ = Spec.map (CommRingCat.ofHom toκ) := rfl

  haveI : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) ↥(IgusaScheme.chartAlgFin N₀ p) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ p).1
  haveI : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) ↥(IgusaScheme.chartAlgInf N₀ p) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ p).2
  haveI : IsProper (toBase0 N₀ p) := ModularCurve.IgusaScheme.isProper_igusaTo N₀ p
  haveI : IsProper (toBase N₀ p) := 𝔓.isProper
  haveI : IsProper (baseChange (R p) (toBase N₀ p) κ) := by
    dsimp only [SmoothProperCurve.baseChange]; infer_instance
  haveI : IsProper (baseChange (R p) (toBase0 N₀ p) κ) := by
    dsimp only [SmoothProperCurve.baseChange]; infer_instance
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) κ) :=
    ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_residue N₀ p hpN₀ κ toκ
  haveI : GeometricallyIntegral (toBase0 N₀ p) := ModularCurve.IgusaScheme.geometricallyIntegral_igusaTo N₀ p hpN₀
  haveI : GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) κ) := by
    dsimp only [SmoothProperCurve.baseChange]; infer_instance

  let ε₀κ : Spec (CommRingCat.of κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ) :=
    pullback.lift (specMap (R p) κ ≫ ε₀.1) (𝟙 _) (by rw [Category.assoc, ε₀.2, Category.comp_id]; rfl)
  have hε₀κ₁ : ε₀κ ≫ pullback.fst _ _ = specMap (R p) κ ≫ ε₀.1 := pullback.lift_fst _ _ _
  have hε₀κ₂ : ε₀κ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hε₁ : ε₀κ ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = sectionFibre 𝔓.εinf (algebraMap (R p) κ) := by
    have hε : ε₀κ = 𝔓.εinf0 (algebraMap (R p) κ) := by
      apply pullback.hom_ext
      · rw [hε₀κ₁]
        simp only [DRModelPackageLevel.εinf0, fibreMap0, sectionFibre, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc]
        rw [hcusp]
      · rw [hε₀κ₂]
        simp only [DRModelPackageLevel.εinf0, fibreMap0, sectionFibre, Category.assoc, pullback.lift_snd,
          pullback.lift_snd_assoc, Category.comp_id]
    rw [hε]
    exact 𝔓.εinf0_comp0 κ (algebraMap (R p) κ)

  obtain ⟨hcard, hpos, hDκ, hPκ, hD₀κ, hP₀κ, hε₁', τ, abq, habq₀, habq₁, hτci, hτmul, habqmul, habqflat, habqsurj, hker⟩ :=
    ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_torus_abq_specialFibre N₀ p hpN₀ 𝔓 κ D hD ε₀ D₀ hD₀
      ε₀κ hε₀κ₁ hε₀κ₂ hε₁

  let φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ) :=
    𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)
  have hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ) := rfl
  have hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ := by
    simp only [φκ, fibreMap0, SmoothProperCurve.baseChange, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact 𝔓.comp_over κ (algebraMap (R p) κ) 1
  obtain ⟨hφfin, hφlfp, hφflat, hφ_rk⟩ :=
    ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_comp_one_pi N₀ p hpN₀ 𝔓 κ (algebraMap (R p) κ)
  haveI : IsFinite φκ := hφfin
  haveI : LocallyOfFinitePresentation φκ := hφlfp
  haveI : Flat φκ := hφflat

  have hFex := ModularCurve.DRModelPackageLevel.exists_frobHom_classifies_normModule_baseChange N₀ p ε₀ D₀ κ hD₀κ
    φκ hφκ_over hφ_rk
  obtain ⟨F, hF, -, -⟩ := hFex

  have habq : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq i))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) t)).obj
            (hDκ.poincare.pullbackAlong a).L)) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;> intro T t a
    ·
      rw [habq₀]
      exact RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
        (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0) hε₁' hDκ hD₀κ t a
    ·
      exact habq₁ t a

  have hrib := ModularCurve.DRModelPackageLevel.baseChange_normHom_eq_restrict_mul_frob_restrict_points N₀ p hpN₀ 𝔓 hrk
    D hD ε₀ D₀ hD₀ hrk_w δ hδ₀ hδ₁ κ hDκ hPκ hD₀κ hP₀κ abq habq φκ hφκ hφκ_over hφ_rk F hF

  let strB : (D₀.baseChange κ).P ⟶ Spec (CommRingCat.of κ) := (D₀.baseChange κ).toBase
  let lawB := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)
  let tBB : pullback strB strB ⟶ Spec (CommRingCat.of κ) := pullback.fst strB strB ≫ strB
  let xBB : SchemeHomOver tBB strB := ⟨pullback.fst strB strB, rfl⟩
  let yBB : SchemeHomOver tBB strB := ⟨pullback.snd strB strB, pullback.condition.symm⟩
  let m₀ := lawB.mul tBB xBB (NeronModelInfra.schemeHomOverComp yBB F)
  let m₁ := lawB.mul tBB (NeronModelInfra.schemeHomOverComp xBB F) yBB
  let Mx : pullback strB strB ⟶ pullback strB strB := pullback.lift m₀.1 m₁.1 (m₀.2.trans m₁.2.symm)

  let eB : Spec (CommRingCat.of κ) ⟶ (D₀.baseChange κ).P := (lawB.one (𝟙 _)).1
  have heB : eB ≫ strB = 𝟙 _ := (lawB.one (𝟙 _)).2
  let eBB : Spec (CommRingCat.of κ) ⟶ pullback strB strB := pullback.lift eB eB rfl
  let gK := pullback.fst Mx eBB
  let fK : pullback Mx eBB ⟶ Spec (CommRingCat.of κ) := pullback.snd Mx eBB

  let q : (D.baseChange κ).P ⟶ pullback strB strB :=
    pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)

  have hRS := ModularCurve.DRModelPackageLevel.fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix N₀ p hpN₀ 𝔓 hrk
    D hD ε₀ D₀ hD₀ hrk_w δ hδ₀ hδ₁ κ hDκ hPκ hD₀κ hP₀κ abq habq φκ hφκ hφκ_over hφ_rk F hF hsm hpr₀
  have hδκ₀ : (NeronSpecialFibreInfra.fibreRestrictAlong (specMap (R p) κ) D₀.toBase D.toBase (δ 0)).1 =
      q ≫ Mx ≫ pullback.fst strB strB := hRS.1
  have hδκ₁ : (NeronSpecialFibreInfra.fibreRestrictAlong (specMap (R p) κ) D₀.toBase D.toBase (δ 1)).1 =
      q ≫ Mx ≫ pullback.snd strB strB := hRS.2

  haveI : IsProper strB := by dsimp only [strB, RelativePic0Designation.baseChange]; infer_instance
  haveI : LocallyOfFiniteType strB := inferInstance
  haveI : LocallyOfFiniteType tBB := inferInstance
  have hMx_over : Mx ≫ tBB = tBB := by
    simp only [Mx, tBB, pullback.lift_fst_assoc]
    exact m₀.2
  haveI : LocallyOfFiniteType (Mx ≫ tBB) := by rw [hMx_over]; infer_instance
  haveI : LocallyOfFiniteType Mx := locallyOfFiniteType_of_comp Mx tBB
  haveI : LocallyOfFiniteType fK := by dsimp only [fK]; infer_instance
  have hNFD := ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber N₀ p hpN₀ 𝔓 ε₀ D₀ hD₀ κ hD₀κ
    φκ hφκ hφκ_over hφ_rk F hF
  haveI : Etale fK := by
    refine AlgebraicGeometry.etale_of_forall_dualNumber_eq_comp fK (fun w hw => ?_)
    exact GoodReductionJacobian.RelativeGroupLaw.dualNumber_eq_comp_of_ker_ribetMatrix strB lawB F hNFD w hw

  have hgK_over : gK ≫ pullback.fst strB strB ≫ strB = fK := by
    have h1 : pullback.fst strB strB ≫ strB = Mx ≫ pullback.fst strB strB ≫ strB := by
      simp only [Mx, pullback.lift_fst_assoc]; exact m₀.2.symm
    rw [h1, ← Category.assoc gK Mx, show gK ≫ Mx = fK ≫ eBB from pullback.condition, Category.assoc]
    simp only [eBB, pullback.lift_fst_assoc]
    exact (congrArg (fK ≫ ·) heB).trans (Category.comp_id fK)
  let lawD := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (R p) κ)
  have hsmκ : Smooth (D.baseChange κ).toBase := by
    dsimp only [RelativePic0Designation.baseChange]
    exact MorphismProperty.pullback_snd (P := @Smooth) _ _ hsm
  have hfib : ∀ y : Spec (CommRingCat.of κ) ⟶ pullback Mx eBB, y ≫ fK = 𝟙 _ → IsReduced (pullback q (y ≫ gK)) := by
    intro y hy
    have hb : (y ≫ gK) ≫ pullback.fst strB strB ≫ strB = 𝟙 _ := by rw [Category.assoc, hgK_over, hy]
    exact AlgebraicGeometry.isReduced_pullback_lift_of_forall_iff_exists_torus (D.baseChange κ).toBase strB lawD lawB hsmκ
      abq habqmul habqsurj _ τ hτci hker (y ≫ gK) hb

  have hred : IsReduced (pullback q gK) :=
    AlgebraicGeometry.isReduced_pullback_of_etale_of_forall_isReduced_pullback q gK fK hfib

  haveI : IsReduced (pullback (q ≫ Mx) eBB) :=
    AlgebraicGeometry.isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso Mx eBB q).inv
  have hδκ₀' : (NeronSpecialFibreInfra.fibreRestrictAlong (Spec.map (CommRingCat.ofHom toκ)) D₀.toBase D.toBase (δ 0)).1 =
      (q ≫ Mx) ≫ pullback.fst strB strB := by simpa only [Category.assoc] using hδκ₀
  have hδκ₁' : (NeronSpecialFibreInfra.fibreRestrictAlong (Spec.map (CommRingCat.ofHom toκ)) D₀.toBase D.toBase (δ 1)).1 =
      (q ≫ Mx) ≫ pullback.snd strB strB := by simpa only [Category.assoc] using hδκ₁
  generalize (NeronSpecialFibreInfra.fibreRestrictAlong (Spec.map (CommRingCat.ofHom toκ)) D₀.toBase D.toBase (δ 0)).1 = d0
    at hδκ₀' ⊢
  generalize (NeronSpecialFibreInfra.fibreRestrictAlong (Spec.map (CommRingCat.ofHom toκ)) D₀.toBase D.toBase (δ 1)).1 = d1
    at hδκ₁' ⊢
  subst hδκ₀' hδκ₁'
  obtain ⟨eH⟩ := KerRed56c2139d.nonempty_iso strB (q ≫ Mx) eB heB
  exact AlgebraicGeometry.isReduced_of_isOpenImmersion eH.hom

end S_ModularCurve_DRModelPackageLevel_isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq (solution)
