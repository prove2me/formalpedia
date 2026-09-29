-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.isAlgEquivZero_fibre_of_pullback_toDR_iso_divisorial_of_multidegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/dc2a49fb-49ad-5dda-820c-b43bb1190154

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit

import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_iso_unit_of_eulerChar_sectionsOf_eq_of_ratFunc
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit
import Theorems.Thm_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_isAlgEquivZero_fibre_of_pullback_toDR_iso_divisorial_of_multidegree_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II"
p2m_attr_erase "instance" "DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

open AlgebraicGeometry.RelPicard
open Opposite

universe u

namespace K5bKit

theorem isAlgEquivZero_fibre_of_closedPoint
    {O : Type} [CommRing O] [IsLocalRing O] {κ : Type} [Field κ] (toκ : O →+* κ) (htoκ : Function.Surjective toκ)
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ)) (tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ℤ))
    (M : (pullback c tO).Modules)
    (hκ : IsAlgEquivZero (fibreAt c tO (Spec.map (CommRingCat.ofHom toκ)))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tO) (Spec.map (CommRingCat.ofHom toκ)))).obj M))
    (k : Type) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O))
    (hs : IsLocalRing.closedPoint O ∈ Set.range s.base) :
    IsAlgEquivZero (fibreAt c tO s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tO) s)).obj M) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : O →+* k, s = Spec.map (CommRingCat.ofHom φ) := ⟨(Spec.preimage s).hom, by simp⟩
  have hkerκ : RingHom.ker toκ = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ htoκ)
  have hkerφ : RingHom.ker toκ ≤ RingHom.ker φ := by
    rw [hkerκ]
    obtain ⟨x, hx⟩ := hs
    intro a ha
    have hxa : φ a ∈ x.asIdeal := by
      have : a ∈ ((Spec.map (CommRingCat.ofHom φ)).base x).asIdeal := by rw [hx]; exact ha
      rw [Spec.map_base] at this
      exact this
    have hx0 : x.asIdeal = ⊥ := (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top
    rw [hx0, Ideal.mem_bot] at hxa
    exact hxa
  obtain ⟨ψ, hψ⟩ : ∃ ψ : κ →+* k, ψ.comp toκ = φ :=
    ⟨RingHom.liftOfSurjective toκ htoκ ⟨φ, hkerφ⟩, RingHom.liftOfSurjective_comp toκ htoκ ⟨φ, hkerφ⟩⟩
  subst hψ
  letI : Algebra κ k := ψ.toAlgebra
  have hsplit : Spec.map (CommRingCat.ofHom (ψ.comp toκ)) =
      Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hsplit]
  let sκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom toκ)
  let sψ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ k))
  let aκ := fibreAt c tO sκ
  have h1 := IsAlgEquivZero.baseChange k aκ hκ
  let e : pullback aκ sψ ≅ pullback (pullback.snd c tO) (sψ ≫ sκ) := pullbackLeftPullbackSndIso (pullback.snd c tO) sκ sψ
  have he1 : e.hom ≫ pullback.snd (pullback.snd c tO) (sψ ≫ sκ) = pullback.snd aκ sψ := pullbackLeftPullbackSndIso_hom_snd _ _ _
  have he2 : e.hom ≫ pullback.fst (pullback.snd c tO) (sψ ≫ sκ) = pullback.fst aκ sψ ≫ pullback.fst (pullback.snd c tO) sκ :=
    pullbackLeftPullbackSndIso_hom_fst _ _ _
  have h2 := IsAlgEquivZero.pullback (a := pullback.snd aκ sψ) (a' := fibreAt c tO (sψ ≫ sκ)) e.inv
    (by rw [Iso.inv_comp_eq, ← he1]; rfl) h1
  refine IsAlgEquivZero.of_iso ?_ h2
  exact ((Scheme.Modules.pullbackComp e.inv _).app _) ≪≫ ((Scheme.Modules.pullbackComp _ _).app M) ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc, ← he2, Iso.inv_hom_id_assoc])).app M

noncomputable def pullbackUnitIso' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
  Scheme.Modules.pullbackUnitIso f

theorem nonempty_pullback_iso_pullback_unit_of_iso_comp
    {A B X P : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ X) (e₁ : A ≅ B) (he₁ : e₁.hom ≫ j = i) (g : X ⟶ P) (q : B ⟶ P) (hq : j ≫ g = q)
    (M : P.Modules) (h : Nonempty ((Scheme.Modules.pullback q).obj M ≅ SheafOfModules.unit B.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  obtain ⟨h⟩ := h
  subst he₁; subst hq
  exact ⟨(Scheme.Modules.pullbackComp (e₁.hom ≫ j) g).app M ≪≫
    (Scheme.Modules.pullbackCongr (Category.assoc _ _ _)).app M ≪≫
    ((Scheme.Modules.pullbackComp e₁.hom (j ≫ g)).app M).symm ≪≫
    (Scheme.Modules.pullback e₁.hom).mapIso h ≪≫ Scheme.Modules.pullbackUnitIso e₁.hom ≪≫ (Scheme.Modules.pullbackUnitIso _).symm⟩

end K5bKit

set_option maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (htoκ : Function.Surjective toκ)

    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ c : X0MqComponents 𝔛reg.width,
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c = 0)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (hMinv : Scheme.Modules.IsInvertible M)
    (eM : Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj M ≅
        (List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module))) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O)),
      IsLocalRing.closedPoint O ∈ Set.range s.base →
      IsAlgEquivZero (fibreAt (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) s)
        ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) s)).obj M) := by
  classical
  haveI := 𝔛.isProper
  intro k _ _ s hs
  refine K5bKit.isAlgEquivZero_fibre_of_closedPoint toκ htoκ (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) M ?_ k s hs

  let sκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom toκ)
  let sZ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))
  have hsZ : sκ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) = sZ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; all_goals (congr 2; exact RingHom.ext_int _ _)
  let X := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  let x : X ⟶ Spec (CommRingCat.of κ) := pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  let L : X.Modules := (Scheme.Modules.pullback (DRModel.baseChangeMap toκ)).obj M
  have hL : Scheme.Modules.IsInvertible L := hMinv.pullback _
  have bcm_fst : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _ := by
    delta DRModel.baseChangeMap; rw [pullback.lift_fst, Category.comp_id]
  have bcm_snd : DRModel.baseChangeMap (p := p) toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
    delta DRModel.baseChangeMap; rw [pullback.lift_snd]

  let XO := pullback (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) sκ
  let ecmp : XO ⟶ X := pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, pullback.condition_assoc, hsZ])
  have hecmp1 : ecmp ≫ x = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hecmp2 : ecmp ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcm_fst, pullback.lift_fst]
    · rw [Category.assoc, bcm_snd, pullback.lift_snd_assoc, pullback.condition]
  suffices hX : IsAlgEquivZero x L by
    have h2 := IsAlgEquivZero.pullback (a := x)
      (a' := fibreAt (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) sκ) ecmp hecmp1 hX
    refine IsAlgEquivZero.of_iso ?_ h2
    exact (Scheme.Modules.pullbackComp ecmp _).app M ≪≫ (Scheme.Modules.pullbackCongr hecmp2).app M

  haveI : IsReduced X := DRModel.isReduced_pullback_toBase_of_charP p κ
  have hns : ¬ Smooth x := DRModelPackage.not_smooth_pullback_snd_toBase_of_charP p 𝔛 κ
  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, a, b, 𝒲₀, hi₁, hi₂, hcover, ha, hnode, hinter, hred, -, -, -, -, -, -, -, -, -,
      ⟨f₁, f₂, hf₁, hf₂⟩, -, -⟩ :=
    DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq p 𝔛 κ hns
  haveI := hci₁; haveI := hci₂

  obtain ⟨e0, he0iso, he0base, he0comp⟩ := 𝔛reg.strict_iso_inf
  obtain ⟨e1, he1iso, he1base, he1comp⟩ := 𝔛reg.strict_iso_zero
  haveI := he0iso; haveI := he1iso
  obtain ⟨𝒱⟩ : Nonempty (((𝔛.ratModel κ).C).TwoAffineOpenCover) := by
    haveI := (𝔛.ratModel κ).isIntegral
    haveI := (𝔛.ratModel κ).isProper
    haveI := (𝔛.ratModel κ).smooth
    haveI : GeometricallyIntegral (𝔛.ratModel κ).toBase := geometricallyIntegral_of_isAlgClosed _
    obtain ⟨P⟩ : Nonempty (𝔛.ratModel κ).C := inferInstance
    obtain ⟨𝒱, -⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed κ (𝔛.ratModel κ).toBase P
    exact ⟨𝒱⟩
  have h_inf : Nonempty ((Scheme.Modules.pullback (inv e0 ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toDR)).obj M ≅
      SheafOfModules.unit ((𝔛.ratModel κ).C).ringCatSheaf) :=
    AlgebraicCurve.CurveModel.nonempty_iso_unit_of_eulerChar_sectionsOf_eq_of_ratFunc κ (𝔛.ratModel κ) 𝒱 _ (hMinv.pullback _)
      (DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective p 𝔛 O hϖ κ toκ 𝔛reg
        htoκ m σ pos neg v hv aplus aminus hdeg M hMinv eM 0 e0 he0base 𝒱)
  have h_zero : Nonempty ((Scheme.Modules.pullback (inv e1 ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toDR)).obj M ≅
      SheafOfModules.unit ((𝔛.ratModel κ).C).ringCatSheaf) :=
    AlgebraicCurve.CurveModel.nonempty_iso_unit_of_eulerChar_sectionsOf_eq_of_ratFunc κ (𝔛.ratModel κ) 𝒱 _ (hMinv.pullback _)
      (DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective p 𝔛 O hϖ κ toκ 𝔛reg
        htoκ m σ pos neg v hv aplus aminus hdeg M hMinv eM 1 e1 he1base 𝒱)
  have hq0 : 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ = inv e0 ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toDR := by
    rw [IsIso.eq_inv_comp, he0comp]
  have hq1 : 𝔛.compZero κ ≫ DRModel.baseChangeMap toκ = inv e1 ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toDR := by
    rw [IsIso.eq_inv_comp, he1comp]
  have h₁ := K5bKit.nonempty_pullback_iso_pullback_unit_of_iso_comp i₁ (𝔛.compInf κ) f₁ hf₁ (DRModel.baseChangeMap toκ) _ hq0 M h_inf
  have h₂ := K5bKit.nonempty_pullback_iso_pullback_unit_of_iso_comp i₂ (𝔛.compZero κ) f₂ hf₂ (DRModel.baseChangeMap toκ) _ hq1 M h_zero
  exact TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter hred L hL h₁ h₂

end S_ModularCurve_DRResolvedModelPackage_isAlgEquivZero_fibre_of_pullback_toDR_iso_divisorial_of_multidegree_eq_zero
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_isAlgEquivZero_fibre_of_pullback_toDR_iso_divisorial_of_multidegree_eq_zero (solution)
