-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/35ddf80a-74ab-5877-9568-9f1b0caafc1b

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
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
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_ModularCurve_DRModelPackageLevel_phi_algebraMap_stalk_mem_integers_comp_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackageLevel_ffEquiv_symm_stalkMap_genericPoint_eq_residue_phi

import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.eisensteinMaximalIdeal.isPrime ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instCommRing_H ModularCurve.JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff ModularCurve.JZeroNeronPrimaryTorsionCore.instFlat_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instFiniteType_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFlat_Hff ModularCurve.JZeroNeronDataPrime.instFiniteΦ ModularCurve.JZeroNeronDataPrime.instAddCommGroupΦ ModularCurve.JZeroNeronDataPrime.instModuleΦ ModularCurve.JZeroNeronData.instAddCommGroupΦ ModularCurve.JZeroNeronData.instModuleΦ ModularCurve.JZeroNeronData.instFiniteΦ AlgebraicGeometry.Scheme.Fppf.instLocallyOfFinitePresentationHomDiscretePUnit AlgebraicGeometry.Scheme.Fppf.instFlatHomDiscretePUnit AlgebraicGeometry.Scheme.instAdditiveAbFunctorOppositeFppfConst AlgebraicGeometry.Scheme.instHasIsosFppfPrecoverage_definitions AlgebraicGeometry.Scheme.Fppf.instFullOverForget AlgebraicGeometry.Scheme.instAdditiveAbSheafFppfSmallFppfTopologyConstantSheaf AlgebraicGeometry.Scheme.hasSheafify_smallFppfTopology AlgebraicGeometry.Scheme.instCategoryFppf AlgebraicGeometry.Scheme.instIsCocontinuousFppfOverForgetSmallFppfTopologyOverFppfTopology AlgebraicGeometry.Scheme.instHasTerminalFppf AlgebraicGeometry.Scheme.instIsMultiplicativeLocallyOfFinitePresentation_definitions AlgebraicGeometry.Scheme.abelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.hasExt_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.instLocallyCoverDenseFppfOverForgetOverFppfTopology AlgebraicGeometry.Scheme.Fppf.instFaithfulOverForget AlgebraicGeometry.Scheme.instAddCommGroupFppfCohomology AlgebraicGeometry.Scheme.instHasPullbacksFppfPrecoverage_definitions"
p2m_attr_erase "instance" "FppfCohomologyLES.fppfSheavesIsGrothendieckAbelian ModularCurve.AdmissibleInvariants.instAdd ModularCurve.AdmissibleInvariants.instZero FppfRepresentableGroupSchemeSheaf.instIsCommMonObjSchemeTensorUnit_definitions FppfRepresentableGroupSchemeSheaf.gateTrivialSheafSectionsSubsingleton ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.JZeroNeronObjectAtP.LevelData.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.mk.injEq ModularCurve.JZeroNeronObjectAtP.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.LevelData.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.injEq ModularCurve.JZeroNeronDataPrime.mk.sizeOf_spec ModularCurve.JZeroNeronDataPrime.mk.injEq ModularCurve.JZeroNeronData.mk.injEq ModularCurve.JZeroNeronData.mk.sizeOf_spec ModularCurve.eisensteinEval_heckeGen ModularCurve.modSystem_apply ModularCurve.FppfKummerData.mk.injEq ModularCurve.JKummerRow.mk.injEq ModularCurve.JKummerRow.mk.sizeOf_spec ModularCurve.FppfKummerData.mk.sizeOf_spec FppfCohomologyLES.cohomologyMapAddEquiv_apply FppfCohomologyLES.biprodSESHom_τ₃ FppfCohomologyLES.cohomologyMap_apply FppfCohomologyLES.cohomologyδ_apply FppfCohomologyLES.cohomologyMapAddEquiv_symm_apply FppfCohomologyLES.biprodSESHom_τ₁ ModularCurve.AdmissibleInvariants.zero_h1 ModularCurve.AdmissibleInvariants.add_h0 ModularCurve.AdmissibleInvariants.zero_δ ModularCurve.AdmissibleInvariants.zero_α ModularCurve.AdmissibleInvariants.zero_h0 ModularCurve.AdmissibleInvariants.add_α ModularCurve.AdmissibleInvariants.mk.sizeOf_spec FppfKummerSES.kummerSES_g FppfKummerSES.kummerSES_X₃ ModularCurve.AdmissibleInvariants.genericDefect_zero ModularCurve.AdmissibleInvariants.add_δ ModularCurve.AdmissibleInvariants.add_h1 FppfKummerSES.kummerSES_X₁ ModularCurve.AdmissibleInvariants.mk.injEq ModularCurve.AdmissibleInvariants.eulerDefect_zero FppfKummerSES.kummerSES_X₂ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve~DRModelPackage AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ResMatchLevelCore

private theorem algebraMap_stalkMap_stalkCongr {C X : Scheme.{0}} [IsIntegral C] (f : C ⟶ X) (y : C) (x : X) (hx : x = f.base y)
    (s : X.presheaf.stalk x) :
    algebraMap (C.presheaf.stalk y) C.functionField ((f.stalkMap y).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom s)) =
      (f.stalkMap (genericPoint C)).hom
        ((X.presheaf.stalkSpecializes (hx ▸ f.base.hom.map_specializes (genericPoint_specializes y))).hom s) := by
  subst hx
  change (C.presheaf.stalkSpecializes (genericPoint_specializes y)).hom ((f.stalkMap y).hom
    ((X.presheaf.stalkSpecializes (specializes_refl (f.base y))).hom s)) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.stalkSpecializes_stalkMap f _ _ (genericPoint_specializes y),
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

private theorem algebraMap_functionField_stalkSpecializes {X : Scheme.{0}} [IsIntegral X] {ξ x : X} (h : ξ ⤳ x)
    (s : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk ξ) X.functionField ((X.presheaf.stalkSpecializes h).hom s) =
      algebraMap (X.presheaf.stalk x) X.functionField s := by
  change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes h).hom s) = (X.presheaf.stalkSpecializes _).hom s
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

private theorem stalkCongr_stalkSpecializes {X : Scheme.{0}} {ξ ξ' x : X} (h : ξ ⤳ x) (e : ξ = ξ') (h' : ξ' ⤳ x)
    (s : X.presheaf.stalk x) :
    (X.presheaf.stalkCongr (.of_eq e)).hom.hom ((X.presheaf.stalkSpecializes h).hom s) = (X.presheaf.stalkSpecializes h').hom s := by
  show (X.presheaf.stalkSpecializes (Inseparable.of_eq e).ge).hom ((X.presheaf.stalkSpecializes h).hom s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

private theorem mem_nonunits_iff_mem_maximalIdeal_of_forall {S L F : Type*} [CommRing S] [IsLocalRing S] [Field L] [Field F]
    (a : S →+* L) (φ : L →+* F) (V : ValuationSubring F)
    (hV : ∀ u, φ (a u) ∈ V ∧ (u ∈ IsLocalRing.maximalIdeal S → φ (a u) ∈ V.nonunits)) (u : S) :
    φ (a u) ∈ V.nonunits ↔ u ∈ IsLocalRing.maximalIdeal S := by
  refine ⟨fun hn => ?_, fun hu => (hV u).2 hu⟩
  by_contra hu
  have hunit : IsUnit u := not_not.mp ((IsLocalRing.mem_maximalIdeal u).not.mp hu)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  have h1 : (⟨φ (a u), (hV u).1⟩ : V) * ⟨φ (a v), (hV v).1⟩ = 1 :=
    Subtype.ext (by rw [V.coe_mul, ← map_mul, ← map_mul, hv, map_one, map_one]; rfl)
  have h2 : IsUnit (⟨φ (a u), (hV u).1⟩ : V) := IsUnit.of_mul_eq_one _ h1
  exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hn) h2

private theorem algebraMap_germ_top_eq {X : Scheme.{0}} [IsIntegral X] (x y : X) (c : Γ(X, ⊤)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ ⊤ x trivial).hom c) =
      algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.germ ⊤ y trivial).hom c) := by
  change ((X.presheaf.germ ⊤ x trivial) ≫ X.presheaf.stalkSpecializes _).hom c =
    ((X.presheaf.germ ⊤ y trivial) ≫ X.presheaf.stalkSpecializes _).hom c
  rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]

end ResMatchLevelCore

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}

    (fm : CharPModel.FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (hfin : ∀ b : IgusaScheme.chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hinf : ∀ b : IgusaScheme.chartAlgInf N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BInf)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ModularPolynomialData d)
    (hsepΦ : (((dataAll N₀ (dvd_refl N₀)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N₀ data hKr (ResidueField ↥A) (residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace hred dataAll hsepΦ)
    (R : ProlongationTuple P)
    (hR : R.IsModel)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))

    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))
    (P₀ P₁ : closedPoints ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C)
    (hP₀ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₀.1 = (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hP₁ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₁.1 = (pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hx₀ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base P₀.1)
    (hx₁ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base P₁.1)
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)
    (hsp₁ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)

    (w : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) (hw : w ∈ ssPlaces q N₀ (ResidueField ↥A))
    (hn : ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO) n : ↥(ssPlaces q N₀ (ResidueField ↥A))) : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = w)

    (tF : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x)
    (htF : φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun N₀ q - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N₀ q ^ q)
    (hor : ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x, φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.nodeIntegers w) :
    ∀ s : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x,

      (R.nodeResidue₁ w ⟨_, hconv s⟩ = 0 ↔
        s ∈ Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom (IsLocalRing.maximalIdeal _)) ∧
      (R.nodeResidue₂ w ⟨_, hconv s⟩ = 0 ↔
        s ∈ Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _)) ∧

      w.ord (R.nodeResidue₁ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₀).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).stalkMap P₀.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₀)).hom.hom s)))) ∧
      (arithFrobC q (ResidueField ↥A) N₀ • w).ord (R.nodeResidue₂ w ⟨_, hconv s⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₁).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).stalkMap P₁.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom s)))) := by
  classical

  have hφO₀ : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a) := fun a => by
    rw [ResMatchLevelCore.algebraMap_germ_top_eq _ x]
    exact hφO a

  obtain ⟨hV₀, hV₁⟩ := ModularCurve.DRModelPackageLevel.phi_algebraMap_stalk_mem_integers_comp_genericPoint N₀ q hqN hA ρ hρ 𝔓 O eO hϖO
    ρO hρO toκ htoκ P R φ hφO₀ hφj
  have hval₀ := fun u => (hV₀ u).1
  have hval₁ := fun u => (hV₁ u).1

  have hη : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base (genericPoint ↥(𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).C) = genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) :=
    genericPoint_eq_of_isOpenImmersion _
  have hξ₀ : ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) = ((𝔓.efib (ResidueField ↥A) (toκ.comp ρO)) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).C) := by
    simp only [Scheme.Hom.comp_apply]
    rw [hη]
  have hξ₁ : ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) = ((𝔓.efib (ResidueField ↥A) (toκ.comp ρO)) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).C) := by
    simp only [Scheme.Hom.comp_apply]
    rw [hη]
  obtain ⟨hBR₀, hBR₁⟩ := ModularCurve.DRModelPackageLevel.ffEquiv_symm_stalkMap_genericPoint_eq_residue_phi N₀ q hqN hA ρ hρ 𝔓 O eO hϖO
    ρO hρO toκ htoκ P R φ hφO₀ hφj hval₀ hval₁ hξ₀ hξ₁

  obtain ⟨⟨hcl₀, hpl₀⟩, ⟨hcl₁, hpl₁⟩⟩ := 𝔓.node_pin (ResidueField ↥A) (toκ.comp ρO) n
  have hP₀eq : P₀.1 = (inv (𝔓.efib (ResidueField ↥A) (toκ.comp ρO))).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n) := by
    rw [← hP₀, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hP₁eq : P₁.1 = (inv (𝔓.efib (ResidueField ↥A) (toκ.comp ρO))).base ((pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n) := by
    rw [← hP₁, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hplace₀ : (𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).placeOfPoint P₀ = w := by
    rw [← hn, ← hpl₀]; congr 1; exact Subtype.ext hP₀eq
  have hplace₁ : (𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).placeOfPoint P₁ = arithFrobC q (ResidueField ↥A) N₀ • w := by
    rw [← hn, ← hpl₁]; congr 1; exact Subtype.ext hP₁eq
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h1 : R.nodeResidue₁ w ⟨_, hconv s⟩ = 0 ↔
        φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.R₁.integers.nonunits := by
      show R.residue₁ ⟨_, (hconv s).1⟩ = 0 ↔ _
      rw [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
        ← ValuationSubring.coe_mem_nonunits_iff]
    rw [h1, ← ResMatchLevelCore.algebraMap_functionField_stalkSpecializes hsp₀ s, Ideal.mem_comap]
    exact ResMatchLevelCore.mem_nonunits_iff_mem_maximalIdeal_of_forall _ φ R.R₁.integers hV₀ _
  ·
    have h1 : R.nodeResidue₂ w ⟨_, hconv s⟩ = 0 ↔
        φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.R₂.integers.nonunits := by
      show R.residue₂ ⟨_, (hconv s).2.1⟩ = 0 ↔ _
      rw [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective, ← RingHom.mem_ker, RegularProlongation.ker_residue,
        ← ValuationSubring.coe_mem_nonunits_iff]
    rw [h1, ← ResMatchLevelCore.algebraMap_functionField_stalkSpecializes hsp₁ s, Ideal.mem_comap]
    exact ResMatchLevelCore.mem_nonunits_iff_mem_maximalIdeal_of_forall _ φ R.R₂.integers hV₁ _
  ·
    rw [hplace₀]
    congr 1
    show (R.residue₁ ⟨_, (hconv s).1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = _
    rw [ResMatchLevelCore.algebraMap_stalkMap_stalkCongr _ P₀.1 x hx₀ s]
    have key := hBR₀ (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom s)
    rw [ResMatchLevelCore.stalkCongr_stalkSpecializes hsp₀ hξ₀
      (hx₀ ▸ (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO)) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫
        DRLevel.bcMap ρO toκ).base.hom.map_specializes (genericPoint_specializes P₀.1)))] at key
    have hL : (R.residue₁ ⟨_, (hconv s).1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        R.residue₁ ⟨_, hval₀ (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom s)⟩ := by
      congr 1
      apply Subtype.ext
      exact congrArg φ (ResMatchLevelCore.algebraMap_functionField_stalkSpecializes hsp₀ s).symm
    rw [hL]
    exact key.symm
  ·
    rw [hplace₁]
    congr 1
    show (R.residue₂ ⟨_, (hconv s).2.1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = _
    rw [ResMatchLevelCore.algebraMap_stalkMap_stalkCongr _ P₁.1 x hx₁ s]
    have key := hBR₁ (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₁).hom s)
    rw [ResMatchLevelCore.stalkCongr_stalkSpecializes hsp₁ hξ₁
      (hx₁ ▸ (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO)) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫
        DRLevel.bcMap ρO toκ).base.hom.map_specializes (genericPoint_specializes P₁.1)))] at key
    have hL : (R.residue₂ ⟨_, (hconv s).2.1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        R.residue₂ ⟨_, hval₁ (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₁).hom s)⟩ := by
      congr 1
      apply Subtype.ext
      exact congrArg φ (ResMatchLevelCore.algebraMap_functionField_stalkSpecializes hsp₁ s).symm
    rw [hL]
    exact key.symm

end S_ModularCurve_DRModelPackageLevel_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal (solution)
