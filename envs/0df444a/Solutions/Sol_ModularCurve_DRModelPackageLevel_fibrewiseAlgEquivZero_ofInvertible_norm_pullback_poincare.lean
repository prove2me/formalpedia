-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3c7be46a-5ddc-5d4b-9973-038c062bf5ae

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_pullback_ofInvertible_of_iso_normModule_morphismRestrict
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
import Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
import Theorems.Thm_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare.ModularCurve ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one DRModelPackageLevel DRModelPackageLevel.isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one"
namespace H2Reduce
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare.ModularCurve ModularCurve.DRLevel AlgebraicGeometry.RelPicard"

theorem isLocalization_R (p : ℕ) [hp : Fact p.Prime] :
    IsLocalization ((Ideal.span {(p : ℤ)}).primeCompl) (R p) := by
  have hcomp : ∀ s : ℤ, s ∈ (Ideal.span {(p : ℤ)}).primeCompl ↔ s.natAbs.Coprime p := by
    intro s
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out,
      Int.natCast_dvd]
  have hcoe : ∀ z : ℤ, ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) z : GaloisRep.ratLocalizedAt p) : ℚ) = z := fun z => by
    simp
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    rw [hcomp] at hs
    have hs0 : (s : ℚ) ≠ 0 := by
      intro h
      have : s = 0 := by exact_mod_cast h
      subst this
      simp [Nat.coprime_zero_left, hp.out.ne_one] at hs
    have hmem : ((s : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt p := by
      show ((s : ℚ)⁻¹).den.Coprime p
      rw [Rat.inv_intCast_den, if_neg (by exact_mod_cast hs0)]
      exact hs
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) s : GaloisRep.ratLocalizedAt p) : ℚ) * (s : ℚ)⁻¹ = 1
    rw [hcoe, mul_inv_cancel₀ hs0]
  · intro z
    have hz : (z : ℚ).den.Coprime p := z.2
    refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), (hcomp _).mpr (by simpa using hz)⟩⟩, Subtype.ext ?_⟩
    show (z : ℚ) * ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) ((z : ℚ).den : ℤ) : GaloisRep.ratLocalizedAt p) : ℚ) =
      ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) (z : ℚ).num : GaloisRep.ratLocalizedAt p) : ℚ)
    rw [hcoe, hcoe, Int.cast_natCast, Rat.mul_den_eq_num]
  · intro x y h
    refine ⟨1, ?_⟩
    have h' := congrArg (fun w : GaloisRep.ratLocalizedAt p => (w : ℚ)) h
    simp only [hcoe, Int.cast_inj] at h'
    rw [h']

theorem isFractionRing_R (p : ℕ) [hp : Fact p.Prime] : IsFractionRing (R p) ℚ := by
  haveI := isLocalization_R p
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization ((Ideal.span {(p : ℤ)}).primeCompl) (R p) ℚ

theorem injective_of_map_natCast_ne_zero (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] (φ : R p →+* k)
    (hpk : (p : k) ≠ 0) : Function.Injective φ := by
  haveI := isLocalization_R p
  have hcast : ∀ m : ℤ, φ (algebraMap ℤ (R p) m) = (m : k) := fun m => eq_intCast (φ.comp (algebraMap ℤ (R p))) m

  have hchar : ringChar k = 0 := by
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hr | hr
    · exfalso
      by_cases hrp : ringChar k = p
      · exact hpk (by rw [← hrp]; exact ringChar.Nat.cast_ringChar)
      · have hmem : ((ringChar k : ℕ) : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
          rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
          intro hdvd
          exact hrp ((Nat.prime_dvd_prime_iff_eq hp.out hr).mp (by exact_mod_cast hdvd)).symm
        have hu := (IsLocalization.map_units (R p) ⟨_, hmem⟩).map φ
        refine hu.ne_zero ?_
        show φ (algebraMap ℤ (R p) ((ringChar k : ℕ) : ℤ)) = 0
        rw [hcast]
        push_cast
        exact ringChar.Nat.cast_ringChar
    · exact hr
  haveI : CharZero k := (CharP.charP_zero_iff_charZero k).mp (ringChar.eq_iff.mp hchar)
  intro a b hab
  rw [← sub_eq_zero] at hab ⊢
  rw [← map_sub] at hab
  set c := a - b
  obtain ⟨⟨m, s⟩, hc⟩ := IsLocalization.surj ((Ideal.span {(p : ℤ)}).primeCompl) c
  have hm : (m : k) = 0 := by
    have := congrArg φ hc
    rw [map_mul, hab, zero_mul, hcast] at this
    exact this.symm
  have hm0 : m = 0 := by exact_mod_cast hm
  have hs : (algebraMap ℤ (R p) s : R p) ≠ 0 := (IsLocalization.map_units (R p) s).ne_zero
  rw [hm0, map_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_right hs

end ModularCurve.H2Reduce

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one DRModelPackageLevel DRModelPackageLevel.isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one"
namespace H2Reduce
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare.ModularCurve ModularCurve.DRLevel AlgebraicGeometry.RelPicard"

theorem asIdeal_base_eq_ker {A : Type} [CommRing A] {k : Type} [Field k] (φ : CommRingCat.of A ⟶ CommRingCat.of k)
    (y : Spec (CommRingCat.of k)) : ((Spec.map φ).base y).asIdeal = RingHom.ker φ.hom := by
  have hy : y.asIdeal = ⊥ := by
    have := y.2
    exact Ideal.eq_bot_of_prime y.asIdeal
  show (PrimeSpectrum.comap φ.hom y).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, hy, ← RingHom.ker_eq_comap_bot]

end ModularCurve.H2Reduce

open ModularCurve.H2Reduce in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]

    (π₁ π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] [IsIntegral ↑(pullback (toBase N₀ p) D.toBase)]
    (hnorm : ∀ U : (pullback (toBase N₀ p) D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback (toBase N₀ p) D.toBase, U))
    [LocallyOfFiniteType D.toBase]

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf)
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
      hinv) := by
  intro k _ _ s
  haveI := 𝔓.isIntegral

  obtain ⟨V, d, hfl, hlfp, hrk, hVcodim⟩ :=
    ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
      N₀ p hpN₀ 𝔓 ℓ π₂ D
  haveI := hfl
  haveI := hlfp
  by_cases hpk : (p : k) = 0
  ·

    haveI : CharP k p := ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpk)
    have h0 := (ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
      N₀ p hpN₀ 𝔓 ℓ π₁ π₂ D hD hnorm Nm hNm hinv V d hrk hVcodim).1
    exact ModularCurve.DRModelPackageLevel.isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP
      N₀ p hpN₀ 𝔓 D hD _ hinv h0 k s
  ·

    have sqF : IsPullback (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst (toBase N₀ p) D.toBase) := by
      have big : IsPullback ((curveChange π₂.1 π₂.2 D.toBase) ≫ (pullback.snd (toBase N₀ p) D.toBase)) (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) D.toBase (π₂.1 ≫ (toBase N₀ p)) := by
        rw [curveChange_snd, π₂.2]
        exact (IsPullback.of_hasPullback (toBase (N₀ * ℓ) p) D.toBase).flip
      have hcomm : (curveChange π₂.1 π₂.2 D.toBase) ≫ (pullback.fst (toBase N₀ p) D.toBase) = (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) ≫ π₂.1 := by
        simp only [curveChange, pullback.lift_fst]
      exact (IsPullback.of_right big hcomm (IsPullback.of_hasPullback (toBase N₀ p) D.toBase).flip).flip
    haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance
    haveI : Surjective (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @Surjective) sqF inferInstance
    have big2 : IsPullback (((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).ι ≫ (pullback.fst (toBase (N₀ * ℓ) p) D.toBase)) ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) π₂.1 ((((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).ι ≫ (pullback.fst (toBase N₀ p) D.toBase)) :=
      (isPullback_morphismRestrict (curveChange π₂.1 π₂.2 D.toBase) ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).flip.paste_horiz sqF
    have hle : (curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) ≤ (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) ⁻¹ᵁ (π₂.1 ⁻¹ᵁ V) := by
      intro x hx
      show ((pullback.fst (toBase (N₀ * ℓ) p) D.toBase) ≫ π₂.1).base x ∈ V
      rw [sqF.w]
      exact hx
    rw [← Scheme.Hom.resLE_comp_ι (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) hle, ← Scheme.Hom.resLE_comp_ι (pullback.fst (toBase N₀ p) D.toBase) (le_refl ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V))] at big2
    have right : IsPullback (π₂.1 ⁻¹ᵁ V).ι (π₂.1 ∣_ V) π₂.1 V.ι := (isPullback_morphismRestrict π₂.1 V).flip
    have sqFV : IsPullback ((pullback.fst (toBase (N₀ * ℓ) p) D.toBase).resLE (π₂.1 ⁻¹ᵁ V) ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) hle) ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) (π₂.1 ∣_ V)
        ((pullback.fst (toBase N₀ p) D.toBase).resLE V ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) (le_refl _)) := by
      refine IsPullback.of_right big2 ?_ right
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      rw [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, sqF.w, morphismRestrict_ι_assoc]
    haveI : Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) sqFV inferInstance
    haveI : LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqFV inferInstance
    haveI : IsFinite (π₂.1 ∣_ V) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict π₂.1 V).flip inferInstance
    have hrkD : ∀ y : ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V), ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).finrank y = d := fun y => by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqFV y]
      exact hrk _

    obtain ⟨-, -, -, -, -, he⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm
    have hP : Scheme.Modules.IsInvertible hD.poincare.L := hD.poincare.isInvertible
    have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L) := hP.pullback _
    have hMV := he ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) d inferInstance inferInstance hrkD _ hL'

    have hfae : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (s' : Spec (CommRingCat.of k') ⟶ D.P),
        IsAlgEquivZero (fibreAt (toBase (N₀ * ℓ) p) D.toBase s')
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toBase (N₀ * ℓ) p) D.toBase) s')).obj
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) := by
      intro k' _ _ s'
      let e : pullback (pullback.snd (toBase (N₀ * ℓ) p) D.toBase) s' ⟶ pullback (pullback.snd (toBase N₀ p) D.toBase) s' :=
        pullback.map _ _ _ _ (curveChange π₁.1 π₁.2 D.toBase) (𝟙 _) (𝟙 D.P) (by rw [Category.comp_id, curveChange_snd]) (by simp)
      have he' : e ≫ fibreAt (toBase N₀ p) D.toBase s' = fibreAt (toBase (N₀ * ℓ) p) D.toBase s' := by
        simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
      have hfst : e ≫ pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s' = pullback.fst (pullback.snd (toBase (N₀ * ℓ) p) D.toBase) s' ≫ (curveChange π₁.1 π₁.2 D.toBase) := by
        simp only [e, pullback.lift_fst]
      refine IsAlgEquivZero.of_iso ?_ ((hD.poincare_mem k' s').pullback e he')
      exact (Scheme.Modules.pullbackComp _ _).app hD.poincare.L ≪≫
        (Scheme.Modules.pullbackCongr hfst).app hD.poincare.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L).symm

    haveI := isFractionRing_R p
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (s ≫ D.toBase)
    have hinj : Function.Injective φ.hom := injective_of_map_natCast_ne_zero p φ.hom hpk
    have hdim := (AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing ℚ (toBase N₀ p)).2 1
      (fun y => by
        have h := ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one N₀ p hpN₀ 𝔓 y
        exact_mod_cast h)

    have hcomm : (pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s ≫ (pullback.fst (toBase N₀ p) D.toBase)) ≫ (toBase N₀ p) = fibreAt (toBase N₀ p) D.toBase s ≫ Spec.map φ := by
      rw [hφ, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
      rfl
    have hs : ∀ x, (pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s).base x ∈ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) := by
      intro x
      show (pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s ≫ (pullback.fst (toBase N₀ p) D.toBase)).base x ∈ V
      apply hVcodim
      have hgen : (((toBase N₀ p)).base ((pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s ≫ (pullback.fst (toBase N₀ p) D.toBase)).base x)).asIdeal = ⊥ := by
        show (((pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s ≫ (pullback.fst (toBase N₀ p) D.toBase)) ≫ (toBase N₀ p)).base x).asIdeal = ⊥
        rw [hcomm]
        show ((Spec.map φ).base ((fibreAt (toBase N₀ p) D.toBase s).base x)).asIdeal = ⊥
        rw [asIdeal_base_eq_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      have h1 := hdim _ hgen
      exact_mod_cast h1

    exact AlgebraicGeometry.RelPicard.IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict
      π₂.1 π₂.2 _ hL' hfae _ hinv ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) d hrkD hMV k s hs

end S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare (solution)
