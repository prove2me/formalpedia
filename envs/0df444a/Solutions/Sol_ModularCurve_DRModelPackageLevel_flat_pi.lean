-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.flat_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/977559c8-8ca5-51d4-998f-26b5d4b34f09

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
import Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback
import Theorems.Thm_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi
import Theorems.Thm_ModularCurve_IgusaScheme_exists_finiteMapData_ratCurveModel_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
import Theorems.Thm_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgFin_tensor
import Theorems.Thm_ModularCurve_IgusaScheme_ringKrullDim_localization_chartAlgInf_tensor
import Theorems.Thm_Module_free_of_isRegular_of_span_eq_maximalIdeal
import Theorems.Thm_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_flat_pi
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ValuationSubring.instIsAlgClosedResidueField AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal"
p2m_attr_erase "instance" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.ExteriorPower.instModulePresheafAb SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj"
p2m_attr_erase "simp" "PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRLevel.R DRLevel.X DRLevel.toBase DRLevel.X0 DRLevel.toBase0 DRLevel.fibre DRModelPackageLevel IgusaScheme IgusaScheme.chartFinOpen IgusaScheme.chartInfOpen IgusaScheme.isAffineOpen_chartFinOpen IgusaScheme.isAffineOpen_chartInfOpen IgusaScheme.igusaCover IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart mk fibre_reduced comp pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_pi"
namespace FlatPi
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

open scoped TensorProduct

def NoMaxMin (T : Type*) [CommRing T] (q : ℕ) : Prop :=
  ∀ P ∈ (Ideal.span {(q : T)}).minimalPrimes, ¬ P.IsMaximal

def NoChain (T : Type*) [CommRing T] (q : ℕ) : Prop :=
  ∀ 𝔮 𝔭 m : Ideal T, 𝔮.IsPrime → 𝔭.IsPrime → m.IsPrime → (q : T) ∈ 𝔮 → 𝔮 < 𝔭 → ¬ 𝔭 < m

theorem noMaxMin_and_noChain_of_ringKrullDim_eq_one (T : Type*) [CommRing T] (q : ℕ) (hq : (q : T) = 0)
    (hloc : ∀ (m : Ideal T) [m.IsMaximal], ringKrullDim (Localization.AtPrime m) = 1) :
    NoMaxMin T q ∧ NoChain T q := by
  have hspan : Ideal.span {(q : T)} = ⊥ := by rw [hq, Ideal.span_singleton_eq_bot]
  constructor
  · intro P hP hPmax
    rw [hspan] at hP
    haveI := hP.1.1
    have h0 : P.height = 0 := Ideal.height_eq_zero_iff.mpr hP
    have h1 := @hloc P hPmax
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), h0] at h1
    exact absurd h1 (by simp)
  · intro 𝔮 𝔭 m h𝔮 h𝔭 hm _ h1 h2
    obtain ⟨m', hm', hmm'⟩ := Ideal.exists_le_maximal m hm.ne_top
    haveI := hm'.isPrime
    have h2' : 𝔭 < m' := lt_of_lt_of_le h2 hmm'
    have ha := Ideal.height_add_one_le_of_lt_of_isPrime h1
    have hb := Ideal.height_add_one_le_of_lt_of_isPrime h2'
    have hd := @hloc m' hm'
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m' (Localization.AtPrime m')] at hd
    have hd' : m'.height = 1 := by exact_mod_cast hd
    have h3 : 𝔮.height + 1 + 1 ≤ m'.height := (add_le_add ha le_rfl).trans hb
    rw [hd'] at h3
    have h4 : (1 : ℕ∞) + 1 ≤ 𝔮.height + 1 + 1 := by
      gcongr
      exact le_add_self
    have h5 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans h3
    exact absurd h5 (by decide)

theorem noMaxMin_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)}) (h : NoMaxMin T' q) :
    NoMaxMin T q := by
  intro P hP hPmax
  have h1 := Ideal.minimalPrimes_map_of_surjective hf (Ideal.span {(q : T)})
  rw [sup_eq_left.mpr hker, Ideal.map_span, Set.image_singleton, map_natCast] at h1
  have h2 : P.map f ∈ (Ideal.span {(q : T')}).minimalPrimes := h1 ▸ ⟨P, hP, rfl⟩
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective f hf hPmax with htop | hmax
  · exact h2.1.1.ne_top htop
  · exact h _ h2 hmax

theorem noChain_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)}) (h : NoChain T' q) :
    NoChain T q := by
  intro 𝔮 𝔭 m h𝔮 h𝔭 hm hq h1 h2
  have hk𝔮 : RingHom.ker f ≤ 𝔮 := hker.trans ((Ideal.span_singleton_le_iff_mem _).mpr hq)
  have hk𝔭 : RingHom.ker f ≤ 𝔭 := hk𝔮.trans h1.le
  have hkm : RingHom.ker f ≤ m := hk𝔭.trans h2.le
  have hinj : ∀ I J : Ideal T, RingHom.ker f ≤ I → RingHom.ker f ≤ J → I.map f = J.map f → I = J := by
    intro I J hI hJ hIJ
    have := congrArg (Ideal.comap f) hIJ
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  refine h (𝔮.map f) (𝔭.map f) (m.map f) (Ideal.map_isPrime_of_surjective hf hk𝔮)
    (Ideal.map_isPrime_of_surjective hf hk𝔭) (Ideal.map_isPrime_of_surjective hf hkm) ?_ ?_ ?_
  · rw [← map_natCast f q]; exact Ideal.mem_map_of_mem f hq
  · exact lt_of_le_of_ne (Ideal.map_mono h1.le) fun he => h1.ne (hinj _ _ hk𝔮 hk𝔭 he)
  · exact lt_of_le_of_ne (Ideal.map_mono h2.le) fun he => h2.ne (hinj _ _ hk𝔭 hkm he)

theorem noMaxMin_noChain_of_surjective {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (hf : Function.Surjective f) (q : ℕ) (hker : RingHom.ker f ≤ Ideal.span {(q : T)})
    (h : NoMaxMin T' q ∧ NoChain T' q) : NoMaxMin T q ∧ NoChain T q :=
  ⟨noMaxMin_of_surjective f hf q hker h.1, noChain_of_surjective f hf q hker h.2⟩

theorem noMaxMin_noChain_of_tensor {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (q : ℕ)
    (h : NoMaxMin ((R ⧸ Ideal.span {(q : R)}) ⊗[R] A) q ∧ NoChain ((R ⧸ Ideal.span {(q : R)}) ⊗[R] A) q) :
    NoMaxMin A q ∧ NoChain A q := by
  set I : Ideal R := Ideal.span {(q : R)} with hI
  have hmap : I.map (algebraMap R A) = Ideal.span {(q : A)} := by
    rw [hI, Ideal.map_span, Set.image_singleton, map_natCast]
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] (R ⧸ I) := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
  let c : A ⊗[R] (R ⧸ I) ≃ₐ[R] (R ⧸ I) ⊗[R] A := Algebra.TensorProduct.comm R A (R ⧸ I)
  let f : A →+* (R ⧸ I) ⊗[R] A :=
    c.toRingEquiv.toRingHom.comp (e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap R A))))
  have hf : Function.Surjective f :=
    c.toRingEquiv.surjective.comp (e.toRingEquiv.surjective.comp Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker f ≤ Ideal.span {(q : A)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : e.toRingEquiv (Ideal.Quotient.mk _ x) = 0 := c.toRingEquiv.injective (by simpa [f] using hx)
    have h2 : Ideal.Quotient.mk (I.map (algebraMap R A)) x = 0 := e.toRingEquiv.injective (by simpa using h1)
    rw [← hmap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  exact noMaxMin_noChain_of_surjective f hf q hker h

end ModularCurve.DRModelPackageLevel.FlatPi

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRLevel.R DRLevel.X DRLevel.toBase DRLevel.X0 DRLevel.toBase0 DRLevel.fibre DRModelPackageLevel IgusaScheme IgusaScheme.chartFinOpen IgusaScheme.chartInfOpen IgusaScheme.isAffineOpen_chartFinOpen IgusaScheme.isAffineOpen_chartInfOpen IgusaScheme.igusaCover IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart mk fibre_reduced comp pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_pi"
namespace FlatPi
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

open IsLocalRing

theorem free_localizedModule_of_dim_two
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [IsDomain A₀] [IsDomain B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
    (hinj : Function.Injective (algebraMap A₀ B₀)) (q : ℕ)
    (hred : IsReduced (B₀ ⧸ Ideal.span {(q : B₀)}))
    (hnomax : ∀ P ∈ (Ideal.span {(q : B₀)}).minimalPrimes, ¬ P.IsMaximal)
    (hchain : ∀ 𝔮 𝔭' m : Ideal A₀, 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime → (q : A₀) ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m)
    (𝔭 : Ideal A₀) [𝔭.IsPrime] [IsNoetherianRing (Localization.AtPrime 𝔭)]
    (hq𝔪 : (q : Localization.AtPrime 𝔭) ∈ maximalIdeal (Localization.AtPrime 𝔭))
    (hq0 : (q : Localization.AtPrime 𝔭) ≠ 0)
    [IsDomain (Localization.AtPrime 𝔭 ⧸ Ideal.span {(q : Localization.AtPrime 𝔭)})]
    [IsDiscreteValuationRing (Localization.AtPrime 𝔭 ⧸ Ideal.span {(q : Localization.AtPrime 𝔭)})] :
    Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl B₀) := by
  classical
  set A := Localization.AtPrime 𝔭 with hA
  let B := Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)
  haveI : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr hinj
  haveI : IsDomain B := inferInstance
  haveI : Module.Finite A B := inferInstance
  haveI : Algebra.IsIntegral A₀ B₀ := inferInstance

  obtain ⟨t, hspan, hAreg⟩ :=
    IsLocalRing.exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
      (q : A) hq𝔪 hq0
  have ht𝔪 : t ∈ maximalIdeal A := by
    rw [← hspan]; exact Ideal.subset_span (by simp)

  have hqB : algebraMap A B (q : A) = (q : B) := map_natCast _ q
  have hqB0 : (q : B) ≠ 0 := by
    intro h
    apply hq0
    have h1 : algebraMap A B (q : A) = 0 := by rw [hqB, h]
    exact (FaithfulSMul.algebraMap_injective A B) (by rw [h1, map_zero])
  have ha : IsSMulRegular B (algebraMap A B (q : A)) := by
    rw [hqB]; exact fun x y h => mul_left_cancel₀ hqB0 h

  have hmapq : (Ideal.span {(q : B₀)}).map (algebraMap B₀ B) = Ideal.span {algebraMap A B (q : A)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, hqB]
  have hredB : IsReduced (B ⧸ Ideal.span {algebraMap A B (q : A)}) := by
    rw [← hmapq]
    haveI := hred
    exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (B₀ ⧸ Ideal.span {(q : B₀)})
      (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) _ hred

  have h𝔭max : 𝔭.IsMaximal := by
    have hprime : (Ideal.span {(q : A)}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    set 𝔮 : Ideal A₀ := (Ideal.span {(q : A)}).under A₀ with h𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under _ _
    have hq𝔮 : (q : A₀) ∈ 𝔮 := by
      rw [h𝔮, Ideal.under, Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
    have h𝔭eq : (maximalIdeal A).under A₀ = 𝔭 := IsLocalization.AtPrime.comap_maximalIdeal A 𝔭
    have h𝔮le : 𝔮 ≤ 𝔭 := by
      rw [← h𝔭eq]; exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hq𝔪)
    have h𝔮ne : 𝔮 ≠ 𝔭 := by
      intro he
      have h1 : Ideal.span {(q : A)} = maximalIdeal A := by
        rw [← IsLocalization.map_under 𝔭.primeCompl A (Ideal.span {(q : A)}), ← h𝔮, he]
        exact Localization.AtPrime.map_eq_maximalIdeal
      have hF : IsField (A ⧸ Ideal.span {(q : A)}) := by
        rw [h1]; exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
      exact IsDiscreteValuationRing.not_isField _ hF
    by_contra hnm
    obtain ⟨m, hm, h𝔭m⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top inferInstance)
    have hne : 𝔭 ≠ m := fun he => hnm (he ▸ hm)
    exact hchain 𝔮 𝔭 m h𝔮p inferInstance hm.isPrime hq𝔮 (lt_of_le_of_ne h𝔮le h𝔮ne) (lt_of_le_of_ne h𝔭m hne)

  have hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B (q : A)}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B (q : A)}) (algebraMap A B t) ∉ P := by
    intro P hP htP

    set P' : Ideal B := P.comap (Ideal.Quotient.mk _) with hP'
    have hP'min : P' ∈ (Ideal.span {algebraMap A B (q : A)}).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hP, rfl⟩
    haveI hP'p : P'.IsPrime := hP'min.1.1
    have hqP' : algebraMap A B (q : A) ∈ P' := hP'min.1.2 (Ideal.subset_span rfl)
    have htP' : algebraMap A B t ∈ P' := htP

    have hPA : P'.comap (algebraMap A B) = maximalIdeal A := by
      refine ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
      rw [← hspan, Ideal.ofList, Ideal.span_le]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
      rcases hx with rfl | rfl
      · exact hqP'
      · exact htP'

    set P₀ : Ideal B₀ := P'.comap (algebraMap B₀ B) with hP₀
    haveI : P₀.IsPrime := Ideal.IsPrime.comap _
    have hP₀A : P₀.comap (algebraMap A₀ B₀) = 𝔭 := by
      rw [hP₀, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A₀ A B,
        ← Ideal.comap_comap, hPA]
      exact IsLocalization.AtPrime.comap_maximalIdeal A 𝔭
    have hP₀min : P₀ ∈ (Ideal.span {(q : B₀)}).minimalPrimes := by
      have h := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl) B (Ideal.span {(q : B₀)})
      rw [hmapq] at h
      have : P' ∈ Ideal.under B₀ ⁻¹' (Ideal.span {(q : B₀)}).minimalPrimes := h ▸ hP'min
      exact this
    have hP₀max : P₀.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P₀ (hP₀A ▸ h𝔭max)
    exact hnomax P₀ hP₀min hP₀max

  haveI : Nontrivial B := inferInstance
  have hreg : RingTheory.Sequence.IsRegular B [(q : A), t] :=
    RingTheory.Sequence.isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
      (q : A) t hq𝔪 ht𝔪 ha hredB hb
  have hfreeB : Module.Free A B :=
    Module.free_of_isRegular_of_span_eq_maximalIdeal [(q : A), t] hAreg hspan B hreg

  have hloc : IsLocalizedModule 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr inferInstance
  let e₀ : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A₀] B :=
    IsLocalizedModule.iso 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap
  let e : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A] B := LinearEquiv.extendScalarsOfIsLocalization 𝔭.primeCompl A e₀
  exact Module.Free.of_equiv e.symm

end ModularCurve.DRModelPackageLevel.FlatPi

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_flat_pi.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRLevel.R DRLevel.X DRLevel.toBase DRLevel.X0 DRLevel.toBase0 DRLevel.fibre DRModelPackageLevel IgusaScheme IgusaScheme.chartFinOpen IgusaScheme.chartInfOpen IgusaScheme.isAffineOpen_chartFinOpen IgusaScheme.isAffineOpen_chartInfOpen IgusaScheme.igusaCover IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart mk fibre_reduced comp pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_pi"
namespace FlatPi
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine (hU.ringKrullDim_stalk_le x hxU).trans ?_
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ n
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  haveI : SmoothOfRelativeDimension n (Scheme.Opens.ι U ≫ f) := by
    have h : SmoothOfRelativeDimension (0 + n) (Scheme.Opens.ι U ≫ f) := inferInstance
    rwa [Nat.zero_add] at h
  exact SmoothOfRelativeDimension.topologicalKrullDim_le (Scheme.Opens.ι U ≫ f) n

theorem maximalIdeal_stalk_spec_eq_map {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R)) :
    letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk t) =
      t.asIdeal.map (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk t)) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R t
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal t.asIdeal _).symm

section Crux

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

theorem isLocalRing_R : IsLocalRing (DRLevel.R q) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out

include hqN in

theorem toBase0_apply_eq_closedPoint_of_not_ringKrullDim_le_one (y : DRLevel.X0 N₀ q)
    (hdim : ¬ ringKrullDim ((DRLevel.X0 N₀ q).presheaf.stalk y) ≤ 1) :
    (DRLevel.toBase0 N₀ q).base y = @IsLocalRing.closedPoint (DRLevel.R q) _ (isLocalRing_R q) := by
  haveI := isLocalRing_R q
  haveI : IsDiscreteValuationRing (DRLevel.R q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  haveI : IsFractionRing (DRLevel.R q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  obtain ⟨-, hsm, -⟩ := IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo N₀ q hqN
  by_contra hne
  apply hdim
  have hbot : ((DRLevel.toBase0 N₀ q).base y).asIdeal = ⊥ := by
    by_contra hb
    apply hne
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hb inferInstance)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ)))) := by
    have := @smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ hsm
  exact (isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing ℚ (DRLevel.toBase0 N₀ q)).2 1
    (fun z => ringKrullDim_stalk_le_of_smoothOfRelativeDimension (pullback.snd (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ)))) 1 z) y hbot

include hqN in

theorem natCast_mem_maximalIdeal_and_isDiscreteValuationRing_stalk_quotient (y : DRLevel.X0 N₀ q)
    (hdim : ¬ ringKrullDim ((DRLevel.X0 N₀ q).presheaf.stalk y) ≤ 1) :
    (q : (DRLevel.X0 N₀ q).presheaf.stalk y) ∈ IsLocalRing.maximalIdeal _ ∧
    (q : (DRLevel.X0 N₀ q).presheaf.stalk y) ≠ 0 ∧
    ∃ _ : IsDomain ((DRLevel.X0 N₀ q).presheaf.stalk y ⧸
        Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk y)}),
      IsDiscreteValuationRing ((DRLevel.X0 N₀ q).presheaf.stalk y ⧸
        Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk y)}) := by
  haveI := isLocalRing_R q
  have hy := toBase0_apply_eq_closedPoint_of_not_ringKrullDim_le_one N₀ q hqN y hdim
  obtain ⟨-, hsm, hgi, -⟩ := IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo N₀ q hqN
  haveI := hgi
  haveI : IsDiscreteValuationRing (DRLevel.R q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  set f : DRLevel.X0 N₀ q ⟶ Spec (CommRingCat.of (DRLevel.R q)) := DRLevel.toBase0 N₀ q with hf
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  set s : Spec (CommRingCat.of (DRLevel.R q)) := IsLocalRing.closedPoint (DRLevel.R q) with hs

  obtain ⟨z, hz⟩ : y ∈ Set.range (f.fiberι s).base := by
    rw [Scheme.Hom.range_fiberι]; exact hy
  subst hz

  have hSm : Smooth (f.fiberToSpecResidueField s) := by
    delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber
    exact MorphismProperty.pullback_snd _ _ ‹Smooth f›
  have hSmd : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField s) := by
    have := @smoothOfRelativeDimension_isStableUnderBaseChange 1
    delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber
    exact MorphismProperty.pullback_snd _ _ hsm
  have hregD : IsRegularLocalRing ((f.fiber s).presheaf.stalk z) :=
    @Smooth.isRegularLocalRing_stalk _ _ _ (f.fiberToSpecResidueField s) hSm z
  have hdimD : ringKrullDim ((f.fiber s).presheaf.stalk z) ≤ 1 :=
    @ringKrullDim_stalk_le_of_smoothOfRelativeDimension _ _ _ (f.fiberToSpecResidueField s) 1 hSmd z

  have hregA : IsRegularLocalRing ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z)) :=
    Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing (DRLevel.R q) f _

  have hsurj : Function.Surjective ((f.fiberι s).stalkMap z).hom := (f.fiberι s).stalkMap_surjective z
  have hker : RingHom.ker ((f.fiberι s).stalkMap z).hom =
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))} := by
    rw [ker_fiberIota_stalkMap_eq_maximalIdeal_map f s z, maximalIdeal_stalk_spec_eq_map, Ideal.map_map]
    have hfx : (f.base ((f.fiberι s).base z)).asIdeal = Ideal.span {(q : DRLevel.R q)} := by
      rw [hy]
      exact GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q Fact.out
    rw [hfx, Ideal.map_span, Set.image_singleton, map_natCast]

  let e : ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) ≃+*
        (f.fiber s).presheaf.stalk z :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI hdomQ : IsDomain ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) :=
    MulEquiv.isDomain _ e.toMulEquiv
  have hregQ : IsRegularLocalRing ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have hdimQ : ringKrullDim ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]; exact hdimD

  have hqmax : (q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z)) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have htop := Ideal.span_singleton_eq_top.mpr hu
    haveI := Ideal.Quotient.subsingleton_iff.mpr htop
    exact not_subsingleton ((f.fiber s).presheaf.stalk z) e.symm.toEquiv.subsingleton

  have hQnf : ¬ IsField ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸
      Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) := by
    intro hF
    apply hdim
    have hmax := Ideal.Quotient.maximal_of_isField _ hF

    have heq := (IsLocalRing.eq_maximalIdeal hmax).symm
    rw [← hregA.spanFinrank_maximalIdeal, heq]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))
      (M := (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))
      (Set.finite_singleton (q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z)))
    rw [Set.ncard_singleton] at h1
    exact_mod_cast h1

  have hq0 : (q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z)) ≠ 0 := by
    intro h0
    apply hdim
    have hbot : Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))} = ⊥ := by
      rw [h0]; exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [← ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _))]
    exact hdimQ

  haveI := hregQ
  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))})).mp hregQ
  have hle : Module.finrank (IsLocalRing.ResidueField ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))})) (IsLocalRing.CotangentSpace ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))})) ≤ 1 := by
    have h : (Module.finrank (IsLocalRing.ResidueField ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))})) (IsLocalRing.CotangentSpace ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))})) : WithBot ℕ∞) ≤ 1 := by
      rw [hfin]; exact hdimQ
    exact_mod_cast h
  refine ⟨hqmax, hq0, hdomQ, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · exact absurd (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0) hQnf
  · exact ((IsDiscreteValuationRing.TFAE ((DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z) ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk ((f.fiberι s).base z))}) hQnf).out 0 5).mpr h1

end Crux

end ModularCurve.DRModelPackageLevel.FlatPi

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_flat_pi.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRLevel.R DRLevel.X DRLevel.toBase DRLevel.X0 DRLevel.toBase0 DRLevel.fibre DRModelPackageLevel IgusaScheme IgusaScheme.chartFinOpen IgusaScheme.chartInfOpen IgusaScheme.isAffineOpen_chartFinOpen IgusaScheme.isAffineOpen_chartInfOpen IgusaScheme.igusaCover IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart mk fibre_reduced comp pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_pi"
namespace FlatPi
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

section Charts
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

noncomputable def ΓChartFinIso (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : V = chartFinOpen N ℓ) :
    Γ(ModularCurve.IgusaScheme N ℓ, V) ≅ CommRingCat.of ↥(chartAlgFin N ℓ) :=
  (ModularCurve.IgusaScheme N ℓ).presheaf.mapIso (eqToIso (congrArg op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιFin N ℓ)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin N ℓ))

noncomputable def ΓChartInfIso (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : V = chartInfOpen N ℓ) :
    Γ(ModularCurve.IgusaScheme N ℓ, V) ≅ CommRingCat.of ↥(chartAlgInf N ℓ) :=
  (ModularCurve.IgusaScheme N ℓ).presheaf.mapIso (eqToIso (congrArg op hV)) ≪≫
    (IsOpenImmersion.ΓIsoTop (ιInf N ℓ)).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf N ℓ))

theorem isDomain_sections_of_eq_chartFinOpen (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : V = chartFinOpen N ℓ) :
    IsDomain Γ(ModularCurve.IgusaScheme N ℓ, V) :=
  (ΓChartFinIso N ℓ V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

theorem isDomain_sections_of_eq_chartInfOpen (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : V = chartInfOpen N ℓ) :
    IsDomain Γ(ModularCurve.IgusaScheme N ℓ, V) :=
  (ΓChartInfIso N ℓ V hV).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

end Charts

section Pi

attribute [local instance] DRModelPackageLevel.neZero_mul

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_jChartFin : 𝔓.iota0 (jChartFin N₀ q) = jChartFin (N₀ * q) q := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iota0_spec (jChartFin N₀ q), coe_jChartFin, coe_jChartFin, coe_jFull, coe_jFull]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_jInvChartInf : 𝔓.iotaInf (jInvChartInf N₀ q) = jInvChartInf (N₀ * q) q := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iotaInf_spec (jInvChartInf N₀ q), coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv,
    IntermediateField.coe_inv, coe_jFull, coe_jFull]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iota0_injective : Function.Injective 𝔓.iota0 := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔓.iota0_spec a, ← 𝔓.iota0_spec b, h]

set_option synthInstance.maxHeartbeats 1600000 in
theorem iotaInf_injective : Function.Injective 𝔓.iotaInf := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  rw [← 𝔓.iotaInf_spec a, ← 𝔓.iotaInf_spec b, h]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιFin :
    𝔓.π.1.base ⁻¹' Set.range (ιFin N₀ q).base = Set.range (ιFin (N₀ * q) q).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q x with h | ⟨y, rfl⟩
    · exact h
    · have e : 𝔓.π.1.base ((ιInf (N₀ * q) q).base y) =
          (ιInf N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔓.pi_chartInf, Scheme.Hom.comp_apply]
      have hx' : (ιInf N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y) ∈
          Set.range (ιFin N₀ q).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y ∈ ιInf N₀ q ⁻¹ᵁ chartFinOpen N₀ q := hx'
      rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen N₀ q).1] at h0
      have h0' : jInvChartInf N₀ q ∉ ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jInvChartInf (N₀ * q) q ∉ y.asIdeal := by
        rw [← iotaInf_jInvChartInf 𝔓]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιInf (N₀ * q) q ⁻¹ᵁ chartFinOpen (N₀ * q) q := by
        rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N₀ * q) q).1]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
  · rintro _ ⟨y, rfl⟩
    show 𝔓.π.1.base ((ιFin (N₀ * q) q).base y) ∈ Set.range (ιFin N₀ q).base
    rw [← Scheme.Hom.comp_apply, 𝔓.pi_chart, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_range_ιInf :
    𝔓.π.1.base ⁻¹' Set.range (ιInf N₀ q).base = Set.range (ιInf (N₀ * q) q).base := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q x with ⟨y, rfl⟩ | h
    · have e : 𝔓.π.1.base ((ιFin (N₀ * q) q).base y) =
          (ιFin N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y) := by
        rw [← Scheme.Hom.comp_apply, 𝔓.pi_chart, Scheme.Hom.comp_apply]
      have hx' : (ιFin N₀ q).base ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y) ∈
          Set.range (ιInf N₀ q).base := by rw [← e]; exact hx
      have h0 : (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y ∈ ιFin N₀ q ⁻¹ᵁ chartInfOpen N₀ q := hx'
      rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen N₀ q).2] at h0
      have h0' : jChartFin N₀ q ∉ ((Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom)).base y).asIdeal :=
        (PrimeSpectrum.mem_basicOpen _ _).mp h0
      have h1 : jChartFin (N₀ * q) q ∉ y.asIdeal := by
        rw [← iota0_jChartFin 𝔓]
        intro hmem
        exact h0' (Ideal.mem_comap.mpr hmem)
      have h2 : y ∈ ιFin (N₀ * q) q ⁻¹ᵁ chartInfOpen (N₀ * q) q := by
        rw [(ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N₀ * q) q).2]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
      exact h2
    · exact h
  · rintro _ ⟨y, rfl⟩
    show 𝔓.π.1.base ((ιInf (N₀ * q) q).base y) ∈ Set.range (ιInf N₀ q).base
    rw [← Scheme.Hom.comp_apply, 𝔓.pi_chartInf, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem preimage_chartFinOpen : 𝔓.π.1 ⁻¹ᵁ chartFinOpen N₀ q = chartFinOpen (N₀ * q) q :=
  TopologicalSpace.Opens.ext (preimage_range_ιFin 𝔓)

theorem preimage_chartInfOpen : 𝔓.π.1 ⁻¹ᵁ chartInfOpen N₀ q = chartInfOpen (N₀ * q) q :=
  TopologicalSpace.Opens.ext (preimage_range_ιInf 𝔓)

theorem appLE_congrHom {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

theorem injective_appTop_specMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective ((Spec.map (CommRingCat.ofHom φ)).appTop).hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h' : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h']
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective.comp
    (hφ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective)

theorem bijective_appLE_opensRange_top {X Y : Scheme} (ι : X ⟶ Y) [IsOpenImmersion ι]
    (e : (⊤ : X.Opens) ≤ ι ⁻¹ᵁ ι.opensRange) : Function.Bijective (ι.appLE ι.opensRange ⊤ e).hom := by
  haveI : IsIso (ι.app ι.opensRange) := ι.isIso_app _ le_rfl
  have htop : ι ⁻¹ᵁ ι.opensRange = ⊤ := ι.preimage_opensRange
  have hid : (homOfLE e).op = (eqToHom htop.symm).op := Subsingleton.elim _ _
  have : IsIso (ι.appLE ι.opensRange ⊤ e) := by
    rw [Scheme.Hom.appLE, hid, eqToHom_op]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (ι.appLE ι.opensRange ⊤ e)

theorem injective_app_opensRange_of_sq {X Y U V : Scheme} (π : X ⟶ Y) (ι : U ⟶ Y) (ι' : V ⟶ X) (σ : V ⟶ U)
    [IsOpenImmersion ι] [IsOpenImmersion ι'] (hsq : ι' ≫ π = σ ≫ ι)
    (hσ : Function.Injective (σ.appTop).hom) : Function.Injective (π.app ι.opensRange).hom := by
  have e₃ : (⊤ : U.Opens) ≤ ι ⁻¹ᵁ ι.opensRange := fun x _ => ⟨x, rfl⟩
  have e₁ : (⊤ : V.Opens) ≤ ι' ⁻¹ᵁ (π ⁻¹ᵁ ι.opensRange) := by
    intro x _
    show π.base (ι'.base x) ∈ Set.range ι.base
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have e₄ : (⊤ : V.Opens) ≤ σ ⁻¹ᵁ ⊤ := le_top.trans (le_of_eq (TopologicalSpace.Opens.map_top _).symm)
  have h1 : π.app ι.opensRange ≫ ι'.appLE (π ⁻¹ᵁ ι.opensRange) ⊤ e₁ = (ι' ≫ π).appLE ι.opensRange ⊤ (by exact e₁) := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (ι' ≫ π).appLE ι.opensRange ⊤ (by exact e₁) = (σ ≫ ι).appLE ι.opensRange ⊤ (hsq ▸ (by exact e₁)) :=
    appLE_congrHom hsq _ _ _
  have h3 : ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appLE ⊤ ⊤ e₄ = (σ ≫ ι).appLE ι.opensRange ⊤ (hsq ▸ (by exact e₁)) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h4 : σ.appLE ⊤ ⊤ e₄ = σ.appTop := by
    have hid : (homOfLE e₄).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, hid]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hcomp : π.app ι.opensRange ≫ ι'.appLE (π ⁻¹ᵁ ι.opensRange) ⊤ e₁ = ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appTop := by
    rw [h1, h2, ← h3, h4]
  have hinj : Function.Injective (ι.appLE ι.opensRange ⊤ e₃ ≫ σ.appTop).hom := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hσ.comp (bijective_appLE_opensRange_top ι e₃).1
  rw [← hcomp] at hinj
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj
  exact Function.Injective.of_comp hinj

theorem injective_app_chartFinOpen : Function.Injective (𝔓.π.1.app (chartFinOpen N₀ q)).hom :=
  injective_app_opensRange_of_sq 𝔓.π.1 (ιFin N₀ q) (ιFin (N₀ * q) q) (Spec.map (CommRingCat.ofHom 𝔓.iota0.toRingHom))
    𝔓.pi_chart (injective_appTop_specMap 𝔓.iota0.toRingHom (iota0_injective 𝔓))

theorem injective_app_chartInfOpen : Function.Injective (𝔓.π.1.app (chartInfOpen N₀ q)).hom :=
  injective_app_opensRange_of_sq 𝔓.π.1 (ιInf N₀ q) (ιInf (N₀ * q) q) (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom))
    𝔓.pi_chartInf (injective_appTop_specMap 𝔓.iotaInf.toRingHom (iotaInf_injective 𝔓))

end Pi

end ModularCurve.DRModelPackageLevel.FlatPi

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRLevel.R DRLevel.X DRLevel.toBase DRLevel.X0 DRLevel.toBase0 DRLevel.fibre DRModelPackageLevel IgusaScheme IgusaScheme.chartFinOpen IgusaScheme.chartInfOpen IgusaScheme.isAffineOpen_chartFinOpen IgusaScheme.isAffineOpen_chartInfOpen IgusaScheme.igusaCover IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul pi_chart mk fibre_reduced comp pi_chartInf iota0 iota0_spec iotaInf_spec π iotaInf isFinite_and_locallyOfFinitePresentation_pi"
namespace FlatPi
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

open IsLocalRing
open scoped TensorProduct

theorem ker_toRingHom_le {T T' : Type*} [CommRing T] [CommRing T'] (e : T ≃+* T') (I : Ideal T) :
    RingHom.ker e.toRingHom ≤ I := by
  intro x hx
  have hx' : e x = 0 := hx
  rw [map_eq_zero_iff e e.injective] at hx'
  rw [hx']
  exact I.zero_mem

section ChartRings
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

theorem isMaximal_span_natCast_R : (Ideal.span {(ℓ : DRLevel.R ℓ)}).IsMaximal := by
  haveI : IsLocalRing (DRLevel.R ℓ) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  rw [← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast ℓ Fact.out]
  exact IsLocalRing.maximalIdeal.isMaximal _

theorem noMaxMin_noChain_chartAlgFin : NoMaxMin ↥(chartAlgFin N ℓ) ℓ ∧ NoChain ↥(chartAlgFin N ℓ) ℓ := by
  haveI hmax := isMaximal_span_natCast_R ℓ
  letI : Field (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) := Ideal.Quotient.field _
  haveI : CharP (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) ℓ :=
    CharP.quotient (DRLevel.R ℓ) ℓ (mem_nonunits_iff.mpr fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  refine noMaxMin_noChain_of_tensor (R := DRLevel.R ℓ) (A := ↥(chartAlgFin N ℓ)) ℓ
    (noMaxMin_and_noChain_of_ringKrullDim_eq_one _ ℓ ?_ ?_)
  · have h0 : ((ℓ : ℕ) : DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) = 0 := CharP.cast_eq_zero _ ℓ
    rw [← map_natCast (algebraMap (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)})
      ((DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) ⊗[DRLevel.R ℓ] ↥(chartAlgFin N ℓ))) ℓ, h0, map_zero]
  · intro m hm
    exact_mod_cast IgusaScheme.ringKrullDim_localization_chartAlgFin_tensor N ℓ
      (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) m

theorem noMaxMin_noChain_chartAlgInf : NoMaxMin ↥(chartAlgInf N ℓ) ℓ ∧ NoChain ↥(chartAlgInf N ℓ) ℓ := by
  haveI hmax := isMaximal_span_natCast_R ℓ
  letI : Field (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) := Ideal.Quotient.field _
  haveI : CharP (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) ℓ :=
    CharP.quotient (DRLevel.R ℓ) ℓ (mem_nonunits_iff.mpr fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  refine noMaxMin_noChain_of_tensor (R := DRLevel.R ℓ) (A := ↥(chartAlgInf N ℓ)) ℓ
    (noMaxMin_and_noChain_of_ringKrullDim_eq_one _ ℓ ?_ ?_)
  · have h0 : ((ℓ : ℕ) : DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) = 0 := CharP.cast_eq_zero _ ℓ
    rw [← map_natCast (algebraMap (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)})
      ((DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) ⊗[DRLevel.R ℓ] ↥(chartAlgInf N ℓ))) ℓ, h0, map_zero]
  · intro m hm
    exact_mod_cast IgusaScheme.ringKrullDim_localization_chartAlgInf_tensor N ℓ
      (DRLevel.R ℓ ⧸ Ideal.span {(ℓ : DRLevel.R ℓ)}) m

theorem noMaxMin_noChain_sections_of_eq_chartFinOpen (V : (ModularCurve.IgusaScheme N ℓ).Opens)
    (hV : V = chartFinOpen N ℓ) :
    NoMaxMin Γ(ModularCurve.IgusaScheme N ℓ, V) ℓ ∧ NoChain Γ(ModularCurve.IgusaScheme N ℓ, V) ℓ :=
  let e := (ΓChartFinIso N ℓ V hV).commRingCatIsoToRingEquiv
  noMaxMin_noChain_of_surjective e.toRingHom e.surjective ℓ
    (ker_toRingHom_le e _) (noMaxMin_noChain_chartAlgFin N ℓ)

theorem noMaxMin_noChain_sections_of_eq_chartInfOpen (V : (ModularCurve.IgusaScheme N ℓ).Opens)
    (hV : V = chartInfOpen N ℓ) :
    NoMaxMin Γ(ModularCurve.IgusaScheme N ℓ, V) ℓ ∧ NoChain Γ(ModularCurve.IgusaScheme N ℓ, V) ℓ :=
  let e := (ΓChartInfIso N ℓ V hV).commRingCatIsoToRingEquiv
  noMaxMin_noChain_of_surjective e.toRingHom e.surjective ℓ
    (ker_toRingHom_le e _) (noMaxMin_noChain_chartAlgInf N ℓ)

end ChartRings

section PerPoint

set_option synthInstance.maxHeartbeats 1600000

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)
variable (U : (DRLevel.X0 N₀ q).Opens) (hU : IsAffineOpen U) (y : DRLevel.X0 N₀ q) (hy : y ∈ U)

@[reducible] noncomputable def algB₀ : Algebra Γ(DRLevel.X0 N₀ q, U) Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) :=
  (𝔓.π.1.app U).hom.toAlgebra

noncomputable abbrev 𝔭 : Ideal Γ(DRLevel.X0 N₀ q, U) := (hU.primeIdealOf ⟨y, hy⟩).asIdeal

theorem L1_free_of_dim_le_one {A : Type*} [CommRing A] [IsRegularLocalRing A] [IsDomain A] (hdim : ringKrullDim A ≤ 1)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] : Module.Free A M := by
  haveI : IsPrincipalIdealRing A := by
    by_cases hF : IsField A
    · letI := hF.toField
      infer_instance
    · have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
      have hle : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) ≤ 1 := by
        have h : (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : WithBot ℕ∞) ≤ 1 := by
          rw [hreg]; exact hdim
        exact_mod_cast h
      have h1 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · exact absurd (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0) hF
        · exact h1
      haveI : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hF).out 0 5).mpr h1
      infer_instance
  exact Module.free_of_finite_type_torsion_free'

include hqN in

theorem isRegularLocalRing_A : IsRegularLocalRing (Localization.AtPrime (𝔭 U hU y hy)) := by
  haveI : IsDiscreteValuationRing (DRLevel.R q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  obtain ⟨-, hsm, -⟩ := IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo N₀ q hqN
  haveI : Smooth (DRLevel.toBase0 N₀ q) := SmoothOfRelativeDimension.smooth 1 _
  letI := (DRLevel.X0 N₀ q).presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  haveI : IsRegularLocalRing ((DRLevel.X0 N₀ q).presheaf.stalk y) :=
    Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing (DRLevel.R q) (DRLevel.toBase0 N₀ q) y
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔭 U hU y hy).primeCompl ((DRLevel.X0 N₀ q).presheaf.stalk y)
      (Localization.AtPrime (𝔭 U hU y hy))).toRingEquiv

include hU in

theorem finite_B₀ [IsFinite 𝔓.π.1] :
    letI := algB₀ 𝔓 U
    Module.Finite Γ(DRLevel.X0 N₀ q, U) Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) := by
  letI := algB₀ 𝔓 U
  exact (RingHom.finite_algebraMap).mp (by
    simpa [algB₀, RingHom.algebraMap_toAlgebra] using IsFinite.finite_app 𝔓.π.1 U hU)

theorem isTorsionFree_M (hdomA : IsDomain Γ(DRLevel.X0 N₀ q, U)) (hdomB : IsDomain Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔓.π.1.app U).hom) :
    letI := algB₀ 𝔓 U
    Module.IsTorsionFree (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U)) := by
  letI := algB₀ 𝔓 U
  haveI := hdomA
  haveI := hdomB
  haveI : Module.IsTorsionFree Γ(DRLevel.X0 N₀ q, U) Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

include hqN in

theorem free_M_of_not_dim_le_one [IsFinite 𝔓.π.1]
    (hdomA : IsDomain Γ(DRLevel.X0 N₀ q, U)) (hdomB : IsDomain Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔓.π.1.app U).hom)
    (hnomax : NoMaxMin Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) q) (hchain : NoChain Γ(DRLevel.X0 N₀ q, U) q)
    (hdim : ¬ ringKrullDim (Localization.AtPrime (𝔭 U hU y hy)) ≤ 1) :
    letI := algB₀ 𝔓 U
    Module.Free (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U)) := by
  classical
  letI := algB₀ 𝔓 U
  haveI := hdomA
  haveI := hdomB
  haveI := finite_B₀ 𝔓 U hU
  haveI := isRegularLocalRing_A (hqN := hqN) U hU y hy

  letI := (DRLevel.X0 N₀ q).presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  set A := Localization.AtPrime (𝔭 U hU y hy) with hAdef
  let e : A ≃+* (DRLevel.X0 N₀ q).presheaf.stalk y :=
    (IsLocalization.algEquiv (𝔭 U hU y hy).primeCompl A ((DRLevel.X0 N₀ q).presheaf.stalk y)).toRingEquiv
  have heq : e (q : A) = (q : (DRLevel.X0 N₀ q).presheaf.stalk y) := map_natCast e q

  have hdimS : ¬ ringKrullDim ((DRLevel.X0 N₀ q).presheaf.stalk y) ≤ 1 := by rwa [← ringKrullDim_eq_of_ringEquiv e]
  obtain ⟨hq𝔪S, hq0S, hdomS, hdvrS⟩ :=
    natCast_mem_maximalIdeal_and_isDiscreteValuationRing_stalk_quotient N₀ q hqN y hdimS
  haveI := hdomS
  haveI := hdvrS

  have hq𝔪 : (q : A) ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (q : (DRLevel.X0 N₀ q).presheaf.stalk y) := heq ▸ hu.map e
    exact (IsLocalRing.mem_maximalIdeal _).mp hq𝔪S hu'
  have hq0 : (q : A) ≠ 0 := by
    intro h0
    apply hq0S
    rw [← heq, h0, map_zero]
  have hspan : Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk y)} = (Ideal.span {(q : A)}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span {x}) heq.symm
  let ebar : A ⧸ Ideal.span {(q : A)} ≃+*
      (DRLevel.X0 N₀ q).presheaf.stalk y ⧸ Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk y)} :=
    Ideal.quotientEquiv (Ideal.span {(q : A)}) (Ideal.span {(q : (DRLevel.X0 N₀ q).presheaf.stalk y)}) e hspan
  haveI : IsDomain (A ⧸ Ideal.span {(q : A)}) := ebar.toMulEquiv.isDomain _
  haveI : IsDiscreteValuationRing (A ⧸ Ideal.span {(q : A)}) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ebar.symm

  haveI hmaxR := isMaximal_span_natCast_R q
  have hred : IsReduced (Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) ⧸ Ideal.span {(q : Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U))}) := by
    letI : Field (DRLevel.R q ⧸ Ideal.span {(q : DRLevel.R q)}) := Ideal.Quotient.field _
    haveI : CharP (DRLevel.R q ⧸ Ideal.span {(q : DRLevel.R q)}) q :=
      CharP.quotient (DRLevel.R q) q (mem_nonunits_iff.mpr fun hu => hmaxR.ne_top (Ideal.span_singleton_eq_top.mpr hu))
    let κ : Type := AlgebraicClosure (DRLevel.R q ⧸ Ideal.span {(q : DRLevel.R q)})
    let φ : DRLevel.R q →+* κ :=
      (algebraMap (DRLevel.R q ⧸ Ideal.span {(q : DRLevel.R q)}) κ).comp (Ideal.Quotient.mk (Ideal.span {(q : DRLevel.R q)}))
    have hφ : φ (q : DRLevel.R q) = 0 := by
      simp only [φ, map_natCast, CharP.cast_eq_zero]
    haveI : IsReduced (DRLevel.fibre (N₀ := N₀) φ) := 𝔓.fibre_reduced κ φ
    have hV : IsAffineOpen (𝔓.π.1 ⁻¹ᵁ U) := hU.preimage 𝔓.π.1
    have h := AlgebraicGeometry.isReduced_sections_quotient_of_isReduced_pullback φ (q : DRLevel.R q) hφ hmaxR
      (DRLevel.toBase N₀ q) (𝔓.π.1 ⁻¹ᵁ U) hV
    first
      | (rw [map_natCast] at h; exact h)
      | (rw [map_natCast] at h; convert h using 2 <;> first | rfl | simp)
      | (simp only [map_natCast] at h; convert h using 3 <;> first | rfl | simp)

  have hinj' : Function.Injective (algebraMap Γ(DRLevel.X0 N₀ q, U) Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U)) := hinj
  exact free_localizedModule_of_dim_two hinj' q hred hnomax hchain (𝔭 U hU y hy) hq𝔪 hq0

include hqN in

theorem free_M [IsFinite 𝔓.π.1]
    (hdomA : IsDomain Γ(DRLevel.X0 N₀ q, U)) (hdomB : IsDomain Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U))
    (hinj : Function.Injective (𝔓.π.1.app U).hom)
    (hnomax : NoMaxMin Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U) q) (hchain : NoChain Γ(DRLevel.X0 N₀ q, U) q) :
    letI := algB₀ 𝔓 U
    Module.Free (Localization.AtPrime (𝔭 U hU y hy))
      (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U)) := by
  letI := algB₀ 𝔓 U
  by_cases hdim : ringKrullDim (Localization.AtPrime (𝔭 U hU y hy)) ≤ 1
  · haveI := isRegularLocalRing_A (hqN := hqN) U hU y hy
    haveI := hdomA
    haveI : IsDomain (Localization.AtPrime (𝔭 U hU y hy)) := inferInstance
    haveI := finite_B₀ 𝔓 U hU
    haveI : Module.Finite (Localization.AtPrime (𝔭 U hU y hy))
        (LocalizedModule (𝔭 U hU y hy).primeCompl Γ(DRLevel.X N₀ q, 𝔓.π.1 ⁻¹ᵁ U)) := inferInstance
    haveI := isTorsionFree_M 𝔓 U hU y hy hdomA hdomB hinj
    exact L1_free_of_dim_le_one hdim _
  · exact free_M_of_not_dim_le_one 𝔓 U hU y hy hdomA hdomB hinj hnomax hchain hdim

end PerPoint

attribute [local instance] DRModelPackageLevel.neZero_mul

theorem main {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN) : Flat 𝔓.π.1 := by
  obtain ⟨hfin, -⟩ := isFinite_and_locallyOfFinitePresentation_pi N₀ q hqN 𝔓
  haveI := hfin
  haveI : IsLocallyNoetherian (DRLevel.X0 N₀ q) := by
    obtain ⟨hpr, -⟩ := IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo N₀ q hqN
    haveI : IsPrincipalIdealRing (DRLevel.R q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
    exact LocallyOfFiniteType.isLocallyNoetherian (DRLevel.toBase0 N₀ q)
  refine (flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule 𝔓.π.1 fun y => ?_).1
  have hcov := IgusaScheme.igusaCover N₀ q
  have hyU : y ∈ IgusaScheme.chartFinOpen N₀ q ⊔ IgusaScheme.chartInfOpen N₀ q := by rw [hcov]; trivial
  rcases hyU with hy | hy
  · refine ⟨_, IgusaScheme.isAffineOpen_chartFinOpen N₀ q, hy, free_M 𝔓 _ _ y hy ?_ ?_ ?_ ?_ ?_⟩
    · exact isDomain_sections_of_eq_chartFinOpen N₀ q _ rfl
    · exact isDomain_sections_of_eq_chartFinOpen (N₀ * q) q _ (preimage_chartFinOpen 𝔓)
    · exact injective_app_chartFinOpen 𝔓
    · exact (noMaxMin_noChain_sections_of_eq_chartFinOpen (N₀ * q) q _ (preimage_chartFinOpen 𝔓)).1
    · exact (noMaxMin_noChain_sections_of_eq_chartFinOpen N₀ q _ rfl).2
  · refine ⟨_, IgusaScheme.isAffineOpen_chartInfOpen N₀ q, hy, free_M 𝔓 _ _ y hy ?_ ?_ ?_ ?_ ?_⟩
    · exact isDomain_sections_of_eq_chartInfOpen N₀ q _ rfl
    · exact isDomain_sections_of_eq_chartInfOpen (N₀ * q) q _ (preimage_chartInfOpen 𝔓)
    · exact injective_app_chartInfOpen 𝔓
    · exact (noMaxMin_noChain_sections_of_eq_chartInfOpen (N₀ * q) q _ (preimage_chartInfOpen 𝔓)).1
    · exact (noMaxMin_noChain_sections_of_eq_chartInfOpen N₀ q _ rfl).2

end ModularCurve.DRModelPackageLevel.FlatPi

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_flat_pi.ModularCurve.DRModelPackageLevel in
theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) : Flat 𝔓.π.1 :=
  ModularCurve.DRModelPackageLevel.FlatPi.main 𝔓

end S_ModularCurve_DRModelPackageLevel_flat_pi
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_flat_pi (solution)
