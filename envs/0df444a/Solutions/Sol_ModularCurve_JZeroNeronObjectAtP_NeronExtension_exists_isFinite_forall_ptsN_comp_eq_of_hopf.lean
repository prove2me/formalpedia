-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6b8751e5-8193-5ccd-824a-c3a6821af5e1

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Theorems.Thm_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective
import Theorems.Thm_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_isFinite_forall_ptsN_comp_eq_of_hopf
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero PresheafOfModules.ExteriorPower.instModulePresheafAb ValuationSubring.instIsAlgClosedResidueField HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike"
p2m_attr_erase "instance" "CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.DRModelPackage.LegTwoInput.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply"
p2m_attr_erase "simp" "CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

open scoped TensorProduct

namespace ProlongMorGlue

section bcPts_aux

variable {R S H L : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H]
  [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

noncomputable def bcPts_ptEquiv (R S H L : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing H]
    [HopfAlgebra R H] [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] :
    WithConv (S ⊗[R] H →ₐ[S] L) ≃ WithConv (H →ₐ[R] L) :=
  WithConv.congr (AlgHom.liftEquiv R S H L).symm

lemma bcPts_ptEquiv_apply (f : WithConv (S ⊗[R] H →ₐ[S] L)) (h : H) :
    (bcPts_ptEquiv R S H L f).ofConv h = f.ofConv (1 ⊗ₜ[R] h) := rfl

lemma bcPts_ptEquiv_mul (f g : WithConv (S ⊗[R] H →ₐ[S] L)) :
    bcPts_ptEquiv R S H L (f * g) = bcPts_ptEquiv R S H L f * bcPts_ptEquiv R S H L g := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  change (bcPts_ptEquiv R S H L (f * g)) h = (bcPts_ptEquiv R S H L f * bcPts_ptEquiv R S H L g) h
  rw [bcPts_ptEquiv_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
  let 𝓡 := Coalgebra.Repr.arbitrary R h
  rw [← 𝓡.eq]
  simp [TensorProduct.tmul_sum, map_sum, Algebra.TensorProduct.lift_tmul, bcPts_ptEquiv_apply]

end bcPts_aux

section bcPts_generic

variable {R S H L V : Type} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
  [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

lemma bcPts_free_and_card (e : WithConv (H →ₐ[R] L) ≃ V) :
    Module.Free S (S ⊗[R] H) ∧ Nat.card V = Module.finrank S (S ⊗[R] H) ∧ Nat.card V ≠ 0 := by
  haveI : Module.Free S (S ⊗[R] H) := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial (S ⊗[R] H) := Bialgebra.nontrivial S
  have hcard : Nat.card V = Module.finrank S (S ⊗[R] H) := by
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero S (S ⊗[R] H) L,
      Nat.card_congr (WithConv.equiv (S ⊗[R] H →ₐ[S] L)).symm, Nat.card_congr (bcPts_ptEquiv R S H L),
      Nat.card_congr e]
  exact ⟨inferInstance, hcard,
    by rw [hcard]; exact ((Module.finrank_pos_iff_of_free S (S ⊗[R] H)).mpr inferInstance).ne'⟩

end bcPts_generic

open ModularCurve in

lemma bcPts_card_eq_pow (M q : ℕ) [NeZero M] [Fact q.Prime] (V : AddSubgroup (JZero M))
    (hV : V ≤ jZeroTorsion M q) [Finite ↥V] : ∃ n : ℕ, Nat.card ↥V = q ^ n := by
  have hP : IsPGroup q (Multiplicative ↥V) := fun g => ⟨1, by
    have hv := (Submodule.mem_torsionBy_iff _ _).mp (hV (Multiplicative.toAdd g).2)
    have hv' : q • (Multiplicative.toAdd g : ↥V) = 0 := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_nsmul]
      simpa using hv
    rw [pow_one]
    exact (ofAdd_nsmul q (Multiplicative.toAdd g)).symm.trans (congrArg Multiplicative.ofAdd hv')⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  exact ⟨n, hn⟩

set_option maxHeartbeats 1600000 in
open ModularCurve ModularCurve.JZeroNeronObjectAtP in
theorem bcPts (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (V : AddSubgroup (JZero (N₀ * p))) (hV : V ≤ jZeroTorsion (N₀ * p) p)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (he : ∀ f g, e (f * g) = e f + e g)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero (N₀ * p)) = σ • ((e f : ↥V) : JZero (N₀ * p))) :
    ∃ (HA : Type) (_ : CommRing HA) (_ : HopfAlgebra ↥(shRing A) HA) (_ : Module.Finite ↥(shRing A) HA)
        (_ : Module.Free ↥(shRing A) HA) (_ : Module.Flat ↥(shRing A) HA) (_ : Coalgebra.IsCocomm ↥(shRing A) HA)
        (_ : ∃ a : ℕ, Module.finrank ↥(shRing A) HA = p ^ a)
        (eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V)
        (_ : ∀ f g, eA (f * g) = eA f + eA g),
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
          (f g : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
          (∀ h : HA, g h = σ (f h)) →
            ((eA g : ↥V) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : JZero (N₀ * p)) := by
  classical

  letI instAlg : Algebra (baseRing p) ↥(shRing A) := Λ.baseToSh.toAlgebra

  haveI hIST : @IsScalarTower (baseRing p) ↥(shRing A) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    rfl

  let HA : Type := ↥(shRing A) ⊗[baseRing p] H
  obtain ⟨hfree, hcard, hne⟩ :=
    bcPts_free_and_card (R := baseRing p) (S := ↥(shRing A)) (H := H) (L := AlgebraicClosure ℚ) e
  haveI : Module.Free ↥(shRing A) HA := hfree

  let eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V :=
    (bcPts_ptEquiv (baseRing p) ↥(shRing A) H (AlgebraicClosure ℚ)).trans e
  have heA : ∀ f g, eA (f * g) = eA f + eA g := fun f g => by
    change e (bcPts_ptEquiv _ _ _ _ (f * g)) = e (bcPts_ptEquiv _ _ _ _ f) + e (bcPts_ptEquiv _ _ _ _ g)
    rw [bcPts_ptEquiv_mul, he]

  haveI : Finite ↥V := Nat.finite_of_card_ne_zero hne
  have hrank : ∃ a : ℕ, Module.finrank ↥(shRing A) HA = p ^ a := by
    obtain ⟨n, hn⟩ := bcPts_card_eq_pow (N₀ * p) p V hV
    exact ⟨n, by rw [← hcard]; exact hn⟩
  refine ⟨HA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hrank, eA, heA, ?_⟩

  intro σ f g hfg
  exact hgal (σ.restrictScalars ℚ) (bcPts_ptEquiv _ _ _ _ f) (bcPts_ptEquiv _ _ _ _ g)
    (fun h => hfg (1 ⊗ₜ[baseRing p] h))

theorem stepPts
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (H : Type) [CommRing H] [Bialgebra R H]
    (H_W : Type) [CommRing H_W] [Bialgebra R H_W] (π : H →ₐc[R] H_W)
    (P : Type) [CommRing P] [Algebra R P] (qa : H →ₐ[R] P)
    (u : Spec (CommRingCat.of H_W) ⟶ N)
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R))
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN) (h : SchemeHomOver q gN)
    (hh : g = L.mul (pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst q q) rfl h)
        (L.inv (pullback.fst q q ≫ q)
          (GoodReductionJacobian.schemeHomOverComp (pullback.snd q q) pullback.condition.symm h)))
    (hgpts : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C),
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) →
        ∀ ab : Spec (CommRingCat.of C) ⟶ pullback q q,
          ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom) →
          ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom) →
          ab ≫ g.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u)
    (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C)
    (habc : WithConv.toConv (a.comp qa) =
      WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) gN)
    (hx : x.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u)
    (hy : y.1 = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1) :
    (L.mul _ x y).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ h.1 := by

  have hh' : L.mul (pullback.fst q q ≫ q) g
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd q q) pullback.condition.symm h) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst q q) rfl h := by
    rw [hh, L.mul_assoc, L.inv_mul_cancel, L.mul_one]

  have hqa : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => a.commutes r
  have hqb : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => b.commutes r
  let ab : Spec (CommRingCat.of C) ⟶ pullback q q :=
    pullback.lift (Spec.map (CommRingCat.ofHom a.toRingHom)) (Spec.map (CommRingCat.ofHom b.toRingHom))
      (by rw [hqa, hqb])
  have hab : ab ≫ (pullback.fst q q ≫ q) = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [← Category.assoc, pullback.lift_fst, hqa]

  have h1 := congrArg (GoodReductionJacobian.schemeHomOverComp ab hab) hh'
  rw [L.mul_natural] at h1
  have hX : GoodReductionJacobian.schemeHomOverComp ab hab g = x := by
    apply Subtype.ext
    show ab ≫ g.1 = x.1
    rw [hx]
    exact hgpts C a b c habc ab (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hY : GoodReductionJacobian.schemeHomOverComp ab hab
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd q q) pullback.condition.symm h) = y := by
    apply Subtype.ext
    show ab ≫ (pullback.snd q q ≫ h.1) = y.1
    rw [hy, ← Category.assoc, pullback.lift_snd]
  rw [hX, hY] at h1
  have h2 := congrArg Subtype.val h1
  rw [h2]
  show ab ≫ (pullback.fst q q ≫ h.1) = _
  rw [← Category.assoc, pullback.lift_fst]

theorem torsorPts
    {R : Type} [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    {ι : Type} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i, IsLocalRing (H ⧸ Ideal.span {1 - e i}))
    (i₀ : ι) (hε : Coalgebra.counit (R := R) (e i₀) = 1)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra R H₀] (π : H →ₐc[R] H₀)
    (hπ : Function.Surjective π) (hker : RingHom.ker (π : H →ₐ[R] H₀) = Ideal.span {1 - e i₀})
    (i : ι) (C : Type) [CommRing C] [Algebra R C]
    (a b : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] C) :
    ∃! c : H₀ →ₐ[R] C,
      WithConv.toConv (a.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) =
        WithConv.toConv (c.comp (π : H →ₐ[R] H₀)) *
          WithConv.toConv (b.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) := by
  classical
  obtain ⟨-, -, -, ρ, -, hbij, hpts⟩ :=
    HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
      R H ι e he hloc i₀ hε i

  set Φ : (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}) :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀})) ρ (fun _ _ => Commute.all _ _)
    with hΦ
  have hΦl : ∀ x : H ⧸ Ideal.span {1 - e i}, Φ (x ⊗ₜ 1) = x ⊗ₜ 1 := by
    intro x
    rw [hΦ, Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.TensorProduct.includeLeft_apply]
  have hΦr : ∀ y : H ⧸ Ideal.span {1 - e i}, Φ (1 ⊗ₜ y) = ρ y := by
    intro y
    rw [hΦ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hπ' : Function.Surjective (π : H →ₐ[R] H₀) := hπ
  let θ : (H ⧸ Ideal.span {1 - e i₀}) ≃ₐ[R] H₀ :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ')
  have hθ : ∀ x : H, θ (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}) x) = π x := by
    intro x
    simp [θ, Ideal.Quotient.mkₐ_eq_mk]
  have hθ' : ∀ x : H, θ.symm (π x) = Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}) x := by
    intro x
    rw [← hθ, AlgEquiv.symm_apply_apply]

  have key : ∀ w : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C,
      ((Algebra.TensorProduct.lift b w (fun _ _ => Commute.all _ _)).comp Φ) =
        Algebra.TensorProduct.lift b ((Algebra.TensorProduct.lift b w (fun _ _ => Commute.all _ _)).comp ρ)
          (fun _ _ => Commute.all _ _) := by
    intro w
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [AlgHom.comp_apply, hΦ, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, map_mul, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

  let Φe := AlgEquiv.ofBijective Φ hbij
  let ψ : (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C :=
    (Algebra.TensorProduct.lift b a (fun _ _ => Commute.all _ _)).comp (Φe.symm : _ →ₐ[R] _)
  have hψΦ : ∀ z, ψ (Φ z) = Algebra.TensorProduct.lift b a (fun _ _ => Commute.all _ _) z := by
    intro z
    show Algebra.TensorProduct.lift b a (fun _ _ => Commute.all _ _) (Φe.symm (Φ z)) = _
    rw [← AlgEquiv.ofBijective_apply Φ hbij z, AlgEquiv.symm_apply_apply]
  let w : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C := ψ.comp Algebra.TensorProduct.includeRight
  have hψl : ∀ x : H ⧸ Ideal.span {1 - e i}, ψ (x ⊗ₜ 1) = b x := by
    intro x
    rw [← hΦl, hψΦ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hψ : ψ = Algebra.TensorProduct.lift b w (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [Algebra.TensorProduct.lift_tmul, ← hψl]
    show ψ (x ⊗ₜ y) = ψ (x ⊗ₜ 1) * ψ (1 ⊗ₜ y)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hρa : (Algebra.TensorProduct.lift b w (fun _ _ => Commute.all _ _)).comp ρ = a := by
    ext y
    rw [AlgHom.comp_apply, ← hψ, ← hΦr, hψΦ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hrelw : WithConv.toConv (a.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) =
      WithConv.toConv (b.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) * WithConv.toConv (w.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))) := by
    rw [← hρa, hpts C b w, WithConv.toConv_ofConv]
  refine ⟨w.comp (θ.symm : H₀ →ₐ[R] H ⧸ Ideal.span {1 - e i₀}), ?_, ?_⟩
  ·
    dsimp only
    have hc : (w.comp (θ.symm : H₀ →ₐ[R] H ⧸ Ideal.span {1 - e i₀})).comp (π : H →ₐ[R] H₀) = w.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀})) := by
      ext x
      show w (θ.symm (π x)) = w (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}) x)
      rw [hθ']
    rw [hc, mul_comm]
    exact hrelw
  ·
    intro c hc

    set w' : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C := c.comp (θ : H ⧸ Ideal.span {1 - e i₀} →ₐ[R] H₀) with hw'
    have hw'mk : w'.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀})) = c.comp (π : H →ₐ[R] H₀) := by
      ext x
      show c (θ (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}) x)) = c (π x)
      rw [hθ]
    have hrel' : WithConv.toConv (a.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) =
        WithConv.toConv (b.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) * WithConv.toConv (w'.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))) := by
      rw [hw'mk, mul_comm]; exact hc

    have hfac : ∀ v : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C,
        WithConv.toConv (a.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) =
          WithConv.toConv (b.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) * WithConv.toConv (v.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))) →
        (Algebra.TensorProduct.lift b v (fun _ _ => Commute.all _ _)).comp Φ =
          Algebra.TensorProduct.lift b a (fun _ _ => Commute.all _ _) := by
      intro v hv
      rw [key]
      have hva : (Algebra.TensorProduct.lift b v (fun _ _ => Commute.all _ _)).comp ρ = a := by
        apply Ideal.Quotient.algHom_ext R
        rw [hpts C b v, ← hv, WithConv.ofConv_toConv]
      simp_rw [hva]
    have heq : Algebra.TensorProduct.lift b w' (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.lift b w (fun _ _ => Commute.all _ _) := by
      refine DFunLike.ext _ _ (fun z => ?_)
      obtain ⟨y, rfl⟩ := hbij.2 z
      have h1 := congrArg (fun f : (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i}) →ₐ[R] C => f y) ((hfac w' hrel').trans (hfac w hrelw).symm)
      simpa using h1
    have hww : w' = w := by
      ext y
      have h1 := congrArg (fun f : (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] C => f (1 ⊗ₜ y)) heq
      simpa [Algebra.TensorProduct.lift_tmul] using h1
    ext z
    obtain ⟨x, rfl⟩ := θ.surjective z
    show c (θ x) = w (θ.symm (θ x))
    rw [AlgEquiv.symm_apply_apply, ← hww, hw']
    rfl

theorem coi_existsUnique_map_eq_one {S K : Type*} [CommRing S] [Field K] (f : S →+* K)
    {ι : Type*} [Fintype ι] (e : ι → S) (he : CompleteOrthogonalIdempotents e) : ∃! i, f (e i) = 1 := by
  classical
  have h01 : ∀ i, f (e i) = 0 ∨ f (e i) = 1 := fun i =>
    IsIdempotentElem.iff_eq_zero_or_one.mp ((he.idem i).map f)
  have hsum : ∑ i, f (e i) = 1 := by
    rw [← map_sum, he.complete, map_one]
  have hex : ∃ i, f (e i) = 1 := by
    by_contra hne
    push_neg at hne
    have : ∑ i, f (e i) = 0 := Finset.sum_eq_zero (fun i _ => (h01 i).resolve_right (hne i))
    rw [this] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hji
  have := he.ortho hji
  have h0 : f (e j * e i) = 0 := by rw [this, map_zero]
  rw [map_mul, hj, hi, mul_one] at h0
  exact one_ne_zero h0

section G6

theorem mul_val_eq_of_val_eq {R : Type} [CommRing R] {N : Scheme.{0}} {gN : N ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R gN) {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t gN) (x' y' : SchemeHomOver t' gN) (hx : x'.1 = x.1) (hy : y'.1 = y.1) :
    (L.mul t' x' y').1 = (L.mul t x y).1 := by
  subst h
  rw [Subtype.ext hx, Subtype.ext hy]

theorem castOver_mul {R : Type} [CommRing R] {N : Scheme.{0}} {gN : N ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R gN) {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t gN) :
    castOver h (L.mul t x y) = L.mul t' (castOver h x) (castOver h y) := by
  subst h
  rfl

theorem descend_factor
    {R : Type} [CommRing R] [Algebra R (AlgebraicClosure ℚ)]
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [Algebra R ↥(IntermediateField.fixedField I)]
    [IsScalarTower R ↥(IntermediateField.fixedField I) (AlgebraicClosure ℚ)]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (t₂ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of R))
    (ht : Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ))) = t₂)
    {J : Type} [AddCommGroup J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (pt : J → SchemeHomOver t₂ gN)
    (pt_add : ∀ x y : J, pt (x + y) = L.mul _ (pt x) (pt y))
    (pt_inj : ∀ x y : J, (pt x).1 = (pt y).1 → x = y)
    (pt_galois : ∀ σ ∈ I, ∀ x : J,
      (pt (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pt x).1)
    (pt_surj : ∀ y : SchemeHomOver t₂ gN, ∃ x : J, pt x = y)
    (hdesc : ∀ n : J, (∀ σ ∈ I, σ • n = n) →
      ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) gN, (pt n).1 = t₂ ≫ s.1)
    (V : AddSubgroup J)
    (HA : Type) [CommRing HA] [Bialgebra R HA]
    (H₀ : Type) [CommRing H₀] [Bialgebra R H₀] (π : HA →ₐc[R] H₀)
    (eA : WithConv (HA →ₐ[R] AlgebraicClosure ℚ) ≃ ↥V)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(IntermediateField.fixedField I)] AlgebraicClosure ℚ)
      (f g : WithConv (HA →ₐ[R] AlgebraicClosure ℚ)),
      (∀ z : HA, g z = σ (f z)) → ((eA g : ↥V) : J) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : J))
    (u : Spec (CommRingCat.of H₀) ⟶ N)
    (hupts : ∀ f₀ : H₀ →ₐ[R] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ u = (pt ((eA (WithConv.toConv (f₀.comp (π : HA →ₐ[R] H₀))) : ↥V) : J)).1)
    (B : Type) [CommRing B] [Algebra R B] (mk : HA →ₐ[R] B)
    (htors : ∀ a b : B →ₐ[R] AlgebraicClosure ℚ, ∃ c : H₀ →ₐ[R] AlgebraicClosure ℚ,
      WithConv.toConv (a.comp mk) = WithConv.toConv (c.comp (π : HA →ₐ[R] H₀)) * WithConv.toConv (b.comp mk))
    (h : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) gN)
    (hstep : ∀ (a b : B →ₐ[R] AlgebraicClosure ℚ) (c : H₀ →ₐ[R] AlgebraicClosure ℚ),
      WithConv.toConv (a.comp mk) = WithConv.toConv (c.comp (π : HA →ₐ[R] H₀)) * WithConv.toConv (b.comp mk) →
      ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) gN,
        x.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u →
        y.1 = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1 →
        (L.mul _ x y).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ h.1) :
    ∃ φ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) gN,
      ∀ a : B →ₐ[R] AlgebraicClosure ℚ,
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ φ.1 = (pt ((eA (WithConv.toConv (a.comp mk)) : ↥V) : J)).1 := by
  classical

  have hb2 : ∀ b : B →ₐ[R] AlgebraicClosure ℚ, (Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1) ≫ gN = t₂ := by
    intro b
    rw [Category.assoc, h.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← ht]
    congr 2
    exact RingHom.ext fun r => b.commutes r
  choose w hw using fun b : B →ₐ[R] AlgebraicClosure ℚ =>
    pt_surj ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1, hb2 b⟩
  have hw1 : ∀ b : B →ₐ[R] AlgebraicClosure ℚ,
      (pt (w b)).1 = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1 := fun b => congrArg Subtype.val (hw b)

  have hconst : ∀ a b : B →ₐ[R] AlgebraicClosure ℚ,
      ((eA (WithConv.toConv (a.comp mk)) : ↥V) : J) - w a = ((eA (WithConv.toConv (b.comp mk)) : ↥V) : J) - w b := by
    intro a b
    obtain ⟨c, hc⟩ := htors a b
    let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) gN :=
      ⟨Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u, by rw [hupts, ht]; exact (pt _).2⟩
    let y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) gN :=
      ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1, by rw [ht]; exact hb2 b⟩
    have hmul := hstep a b c hc x y rfl rfl
    have hval : (pt (((eA (WithConv.toConv (c.comp (π : HA →ₐ[R] H₀))) : ↥V) : J) + w b)).1 = (pt (w a)).1 := by
      rw [pt_add, hw1 a, ← hmul]
      exact mul_val_eq_of_val_eq L ht x y _ _ (hupts c).symm (hw1 b)
    have hinj := pt_inj _ _ hval
    have hea : ((eA (WithConv.toConv (a.comp mk)) : ↥V) : J) =
        ((eA (WithConv.toConv (c.comp (π : HA →ₐ[R] H₀))) : ↥V) : J) + ((eA (WithConv.toConv (b.comp mk)) : ↥V) : J) := by
      rw [hc, heA_add, AddSubgroup.coe_add]
    rw [hea, ← hinj]
    abel

  by_cases hne : Nonempty (B →ₐ[R] AlgebraicClosure ℚ)
  swap
  · exact ⟨h, fun a => (hne ⟨a⟩).elim⟩
  obtain ⟨b₀⟩ := hne
  set n : J := ((eA (WithConv.toConv (b₀.comp mk)) : ↥V) : J) - w b₀ with hn

  have hninv : ∀ σ ∈ I, σ • n = n := by
    intro σ hσ
    have hfix : ∀ z : ↥(IntermediateField.fixedField I), σ (z : AlgebraicClosure ℚ) = z :=
      fun z => (IntermediateField.mem_fixedField_iff I (z : AlgebraicClosure ℚ)).mp z.2 σ hσ
    let σ' : AlgebraicClosure ℚ ≃ₐ[↥(IntermediateField.fixedField I)] AlgebraicClosure ℚ :=
      { σ with commutes' := fun z => hfix z }
    have hσ' : σ'.restrictScalars ℚ = σ := AlgEquiv.ext fun _ => rfl
    let b₁ : B →ₐ[R] AlgebraicClosure ℚ :=
      ((σ' : AlgebraicClosure ℚ →ₐ[↥(IntermediateField.fixedField I)] AlgebraicClosure ℚ).restrictScalars R).comp b₀
    have hE : ((eA (WithConv.toConv (b₁.comp mk)) : ↥V) : J) = σ • ((eA (WithConv.toConv (b₀.comp mk)) : ↥V) : J) := by
      have h1 := heA_act σ' (WithConv.toConv (b₀.comp mk)) (WithConv.toConv (b₁.comp mk)) (fun _ => rfl)
      rw [hσ'] at h1
      exact h1
    have hb₁ : b₁.toRingHom = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp b₀.toRingHom :=
      RingHom.ext fun _ => rfl
    have hW : w b₁ = σ • w b₀ := by
      apply pt_inj
      rw [hw1, pt_galois σ hσ (w b₀), hw1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb₁]
    rw [hn, smul_sub, ← hE, ← hW]
    exact hconst b₁ b₀

  obtain ⟨s, hs⟩ := hdesc n hninv
  let sB : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) gN :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩
  refine ⟨L.mul _ h sB, fun a => ?_⟩
  have hψ : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => a.commutes r
  have hnat := congrArg Subtype.val (L.mul_natural _ _ (Spec.map (CommRingCat.ofHom a.toRingHom)) hψ h sB)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
  rw [hnat]
  have hkey : ((eA (WithConv.toConv (a.comp mk)) : ↥V) : J) = w a + n := by
    rw [hn, ← hconst a b₀]
    abel
  rw [hkey, pt_add]
  symm
  refine mul_val_eq_of_val_eq L ht _ _ _ _ ?_ ?_
  · rw [hw1]
    rfl
  · rw [hs, ← ht]
    show _ = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ s.1)
    rw [← Category.assoc, hψ]

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A} {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ}

theorem ptsN_add (F : O.NeronExtension) (x y : JZero (N₀ * p)) :
    F.ptsN (x + y) = F.LN.mul _ (F.ptsN x) (F.ptsN y) := by
  show NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x + y))) F.openImm =
    F.LN.mul _ (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) F.openImm)
      (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts y)) F.openImm)
  rw [← F.openImm_mul, O.pts_add]
  congr 1
  simp only [LevelData.shGenLift, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
    castOver_mul]

theorem ptsN_val_injective (F : O.NeronExtension) (x y : JZero (N₀ * p))
    (h : (F.ptsN x).1 = (F.ptsN y).1) : x = y := by
  haveI := F.openImm_isOpenImmersion
  apply O.pts.injective
  apply Subtype.ext
  have h1 : (Λ.shGenLift (O.pts x)).1 = (Λ.shGenLift (O.pts y)).1 := by
    rw [← cancel_mono F.openImm.1]
    exact h
  have h2 := congrArg (fun m => m ≫ pullback.fst O.g Λ.shStr) h1
  simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst] at h2
  exact h2

theorem ptsN_galois (F : O.NeronExtension) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : JZero (N₀ * p)) :
    (F.ptsN (σ • x)).1 =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (F.ptsN x).1 := by
  have hfix : ∀ z : ↥(invField A), σ (z : AlgebraicClosure ℚ) = z :=
    fun z => (IntermediateField.mem_fixedField_iff (A.inertiaSubgroupIn ℚ) (z : AlgebraicClosure ℚ)).mp z.2 σ hσ
  have hring : (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (A.subtype.comp (shToPlace A)) =
      A.subtype.comp (shToPlace A) := by
    ext z
    show σ (((shToPlace A z : ↥A) : AlgebraicClosure ℚ)) = ((shToPlace A z : ↥A) : AlgebraicClosure ℚ)
    rw [coe_shToPlace, hfix]
  have hbase : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (barPt A ≫ shPt A) =
      barPt A ≫ shPt A := by
    show Spec.map _ ≫ Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (shToPlace A)) =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (shToPlace A))
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  show (Λ.shGenLift (O.pts (σ • x))).1 ≫ F.openImm.1 = Spec.map _ ≫ ((Λ.shGenLift (O.pts x)).1 ≫ F.openImm.1)
  rw [← Category.assoc]
  congr 1
  simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact O.pts_galois σ x
  · simp only [Category.assoc, pullback.lift_snd]
    exact hbase.symm

theorem specMap_algebraMap_eq_barPt_shPt [Algebra ↥(shRing A) (AlgebraicClosure ℚ)]
    (halg : ∀ z : ↥(shRing A), algebraMap ↥(shRing A) (AlgebraicClosure ℚ) z = ((z : ↥(invField A)) : AlgebraicClosure ℚ)) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) = barPt A ≫ shPt A := by
  show Spec.map _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (shToPlace A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z
  rw [halg]
  rfl

theorem descend_factor_neron (F : O.NeronExtension) (hΛ : Λ.IsJacobian)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (halg : ∀ z : ↥(shRing A), algebraMap ↥(shRing A) (AlgebraicClosure ℚ) z = ((z : ↥(invField A)) : AlgebraicClosure ℚ))
    (V : AddSubgroup (JZero (N₀ * p)))
    (HA : Type) [CommRing HA] [Bialgebra ↥(shRing A) HA]
    (H₀ : Type) [CommRing H₀] [Bialgebra ↥(shRing A) H₀] (π : HA →ₐc[↥(shRing A)] H₀)
    (eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
      (f g : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
      (∀ z : HA, g z = σ (f z)) →
        ((eA g : ↥V) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : JZero (N₀ * p)))
    (u : Spec (CommRingCat.of H₀) ⟶ F.Nfull)
    (hupts : ∀ f₀ : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ u =
        (F.ptsN ((eA (WithConv.toConv (f₀.comp (π : HA →ₐ[↥(shRing A)] H₀))) : ↥V) : JZero (N₀ * p))).1)
    (B : Type) [CommRing B] [Algebra ↥(shRing A) B] (mk : HA →ₐ[↥(shRing A)] B)
    (htors : ∀ a b : B →ₐ[↥(shRing A)] AlgebraicClosure ℚ, ∃ c : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
      WithConv.toConv (a.comp mk) =
        WithConv.toConv (c.comp (π : HA →ₐ[↥(shRing A)] H₀)) * WithConv.toConv (b.comp mk))
    (h : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) B))) F.gN)
    (hstep : ∀ (a b : B →ₐ[↥(shRing A)] AlgebraicClosure ℚ) (c : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ),
      WithConv.toConv (a.comp mk) =
        WithConv.toConv (c.comp (π : HA →ₐ[↥(shRing A)] H₀)) * WithConv.toConv (b.comp mk) →
      ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ)))) F.gN,
        x.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u →
        y.1 = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1 →
        (F.LN.mul _ x y).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ h.1) :
    ∃ φ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) B))) F.gN,
      ∀ a : B →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ φ.1 =
          (F.ptsN ((eA (WithConv.toConv (a.comp mk)) : ↥V) : JZero (N₀ * p))).1 :=
  descend_factor (A.inertiaSubgroupIn ℚ) F.gN F.LN (barPt A ≫ shPt A) (specMap_algebraMap_eq_barPt_shPt halg)
    F.ptsN (ptsN_add F) (ptsN_val_injective F) (fun σ hσ x => ptsN_galois F σ hσ x) F.openImm_pts_surjective
    (fun n hn =>
      ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_ptsN_eq_comp_of_mem_inertiaInvariants
        N₀ p hpN₀ A hA Λ hΛ O F n (mem_inertiaInvariants.mpr hn))
    V HA H₀ π eA heA_add heA_act u hupts B mk htors h hstep

end G6

end ProlongMorGlue

theorem prolongMor_flat_quotient_span_one_sub {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (e : S) (he : IsIdempotentElem e) : Module.Flat R (S ⧸ Ideal.span {1 - e}) := by
  haveI : IsLocalization.Away e (S ⧸ Ideal.span {1 - e}) :=
    IsLocalization.away_of_isIdempotentElem he
      (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  haveI : Module.Flat S (S ⧸ Ideal.span {1 - e}) := IsLocalization.flat _ (Submonoid.powers e)
  exact Module.Flat.trans R S _

set_option maxHeartbeats 4000000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension)
    (hIU : ∀ (m : ℕ), m.Coprime p →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m)
    (hII : ∀ (m : ℕ), 0 < m →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m)
    (hp2 : p ≠ 2)
    (V : AddSubgroup (JZero (N₀ * p))) (hV : V ≤ jZeroTorsion (N₀ * p) p)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (he : ∀ f g, e (f * g) = e f + e g)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero (N₀ * p)) = σ • ((e f : ↥V) : JZero (N₀ * p))) :
    ∃ (X : Scheme.{0}) (gX : X ⟶ shBase A) (φ : X ⟶ F.Nfull),
      φ ≫ F.gN = gX ∧ IsFinite gX ∧ Flat gX ∧
      (∀ v ∈ V, ∃ x : SchemeHomOver (barPt A ≫ shPt A) gX, x.1 ≫ φ = (F.ptsN v).1) ∧
      (∀ x : SchemeHomOver (barPt A ≫ shPt A) gX, ∃ v ∈ V, x.1 ≫ φ = (F.ptsN v).1) := by
  classical

  obtain ⟨hDVR, hunif, hchar, hsh⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
  haveI : IsDiscreteValuationRing ↥(shRing A) := hDVR
  haveI : CharZero ↥(shRing A) := hchar
  haveI : HenselianLocalRing ↥(shRing A) :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
  haveI : IsAlgClosed (ResidueField ↥(shRing A)) := by

    obtain ⟨-, -, hres, -⟩ := ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed p A hA 1
    let f : ↥(shRing A) →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp (shToPlace A)
    have hf : Function.Surjective f := hres
    haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
    have hmax : RingHom.ker f = maximalIdeal ↥(shRing A) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)
    exact IsAlgClosed.of_ringEquiv _ _
      (((Ideal.quotEquivOfEq hmax.symm).trans (RingHom.quotientKerEquivOfSurjective hf)).symm)
  letI instAlgOA : Algebra ↥(shRing A) (AlgebraicClosure ℚ) :=
    ((algebraMap ↥(invField A) (AlgebraicClosure ℚ)).comp (algebraMap ↥(shRing A) ↥(invField A))).toAlgebra
  haveI : IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  obtain ⟨HA, _instCR, _instHopf, _instFin, _instFree, _instFlat, _instCocomm, hrankA, eA, heA_add, heA_act⟩ :
      ∃ (HA : Type) (_ : CommRing HA) (_ : HopfAlgebra ↥(shRing A) HA) (_ : Module.Finite ↥(shRing A) HA)
        (_ : Module.Free ↥(shRing A) HA) (_ : Module.Flat ↥(shRing A) HA) (_ : Coalgebra.IsCocomm ↥(shRing A) HA)
        (_ : ∃ a : ℕ, Module.finrank ↥(shRing A) HA = p ^ a)
        (eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V)
        (_ : ∀ f g, eA (f * g) = eA f + eA g),
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
          (f g : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
          (∀ h : HA, g h = σ (f h)) →
            ((eA g : ↥V) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : JZero (N₀ * p)) :=
    ProlongMorGlue.bcPts N₀ p A Λ V hV H e he hgal

  obtain ⟨instFt, eI, hCOI, hnot, hin, hlocI⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := ↥(shRing A)) (S := HA)
  obtain ⟨i₀, hi₀, _hi₀u⟩ :=
    Bialgebra.existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents (R := ↥(shRing A)) eI hCOI

  obtain ⟨H₀, _instCR0, _instHopf0, π, hπsurj, hker, hloc0, hfin0, hcocomm0, hflat0⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient
      (R := ↥(shRing A)) (eI i₀) (hCOI.idem i₀) hi₀ (hlocI i₀)
  haveI : Module.Finite ↥(shRing A) H₀ := hfin0
  haveI : Coalgebra.IsCocomm ↥(shRing A) H₀ := hcocomm0 inferInstance
  haveI : Module.Flat ↥(shRing A) H₀ := hflat0 inferInstance
  haveI : Module.Free ↥(shRing A) H₀ := Module.free_of_flat_of_isLocalRing
  have hrank0 : ∃ b : ℕ, Module.finrank ↥(shRing A) H₀ = p ^ b := by

    obtain ⟨a, ha⟩ := hrankA
    have hcardA : Nat.card (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) = p ^ a := by
      rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero, ha]
    have hcard0 : Nat.card (H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ) = Module.finrank ↥(shRing A) H₀ :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero _ _ _
    haveI : Finite (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) :=
      Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    have hdvd : Nat.card (H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ∣ p ^ a := by
      rw [← hcardA]
      exact HopfAlgebra.natCard_algHom_dvd_natCard_algHom_of_surjective ↥(shRing A) (AlgebraicClosure ℚ) HA H₀ π hπsurj
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    exact ⟨b, by rw [← hcard0, hb]⟩

  obtain ⟨u, hu, hmul, hupts⟩ :=
    ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing
      N₀ p hpN₀ A hA Λ hΛ O F hIU hII hp2 V hV HA hrankA eA heA_add heA_act H₀ hloc0 hrank0 π

  have htors : ∀ (i : MaximalSpectrum HA) (C : Type) [CommRing C] [Algebra ↥(shRing A) C]
      (a b : (HA ⧸ Ideal.span {1 - eI i}) →ₐ[↥(shRing A)] C),
      ∃! c : H₀ →ₐ[↥(shRing A)] C,
        WithConv.toConv (a.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))) =
          WithConv.toConv (c.comp (π : HA →ₐ[↥(shRing A)] H₀)) *
            WithConv.toConv (b.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))) := by
    exact fun i C _ _ a b => ProlongMorGlue.torsorPts eI hCOI hlocI i₀ hi₀ H₀ π hπsurj hker i C a b

  haveI : Smooth F.gN := F.hN.smooth
  haveI : IsSeparated F.gN := F.hN.separated
  haveI : LocallyOfFiniteType F.gN := F.hN.locallyOfFiniteType
  haveI : QuasiCompact F.gN := F.hN.quasiCompact
  have step : ∀ i : MaximalSpectrum HA,
      ∃ h : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (HA ⧸ Ideal.span {1 - eI i})))) F.gN,
        ∀ (a b : (HA ⧸ Ideal.span {1 - eI i}) →ₐ[↥(shRing A)] AlgebraicClosure ℚ) (c : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ),
          WithConv.toConv (a.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))) =
            WithConv.toConv (c.comp (π : HA →ₐ[↥(shRing A)] H₀)) *
              WithConv.toConv (b.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))) →
          ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ)))) F.gN,
            x.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u →
            y.1 = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ h.1 →
            (F.LN.mul _ x y).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ h.1 := by
    intro i
    haveI : IsLocalRing (HA ⧸ Ideal.span {1 - eI i}) := hlocI i
    haveI : Module.Flat ↥(shRing A) (HA ⧸ Ideal.span {1 - eI i}) :=
      prolongMor_flat_quotient_span_one_sub (R := ↥(shRing A)) (eI i) (hCOI.idem i)
    obtain ⟨g, hg, hgpts⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
        F.gN F.LN HA H₀ π (HA ⧸ Ideal.span {1 - eI i}) (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))
        (htors i) u hu hmul _ rfl
    obtain ⟨h, hh⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing
        F.gN F.LN F.commN (HA ⧸ Ideal.span {1 - eI i}) _ rfl g hg
    exact ⟨h, fun a b c habc x y hx hy =>
      ProlongMorGlue.stepPts F.gN F.LN HA H₀ π (HA ⧸ Ideal.span {1 - eI i}) (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))
        u _ rfl g h hh hgpts _ a b c habc x y hx hy⟩

  have descend : ∀ i : MaximalSpectrum HA,
      ∃ φ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (HA ⧸ Ideal.span {1 - eI i})))) F.gN,
        ∀ a : (HA ⧸ Ideal.span {1 - eI i}) →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ φ.1 =
            (F.ptsN ((eA (WithConv.toConv (a.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i})))) : ↥V) :
              JZero (N₀ * p))).1 := by
    intro i
    obtain ⟨h, hstep⟩ := step i
    exact ProlongMorGlue.descend_factor_neron F hΛ (fun _ => rfl) V HA H₀ π eA heA_add heA_act u hupts
      (HA ⧸ Ideal.span {1 - eI i}) (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i}))
      (fun a b => (htors i _ a b).exists) h hstep

  choose φI hφI using descend
  obtain ⟨Φ, ⟨hΦover, hΦi⟩, -⟩ :=
    AlgebraicGeometry.existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents
      (R := ↥(shRing A)) eI hCOI F.gN (fun i => (φI i).1) (fun i => (φI i).2)

  have hbase : Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) = barPt A ≫ shPt A := by
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hread : ∀ f : HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Φ = (F.ptsN ((eA (WithConv.toConv f) : ↥V) : JZero (N₀ * p))).1 := by
    intro f
    obtain ⟨i, hi, -⟩ := ProlongMorGlue.coi_existsUnique_map_eq_one f.toRingHom eI hCOI

    have hker : ∀ s ∈ Ideal.span {1 - eI i}, f s = 0 := by
      intro s hs
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      simp [map_mul, map_sub, show f (eI i) = 1 from hi]
    let a : (HA ⧸ Ideal.span {1 - eI i}) →ₐ[↥(shRing A)] AlgebraicClosure ℚ :=
      Ideal.Quotient.liftₐ (Ideal.span {1 - eI i}) f hker
    have ha : a.comp (Ideal.Quotient.mkₐ ↥(shRing A) (Ideal.span {1 - eI i})) = f := Ideal.Quotient.liftₐ_comp _ _ _
    have hSpec : Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - eI i}))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [hSpec, Category.assoc, hΦi i, hφI i a, ha]
  refine ⟨Spec (CommRingCat.of HA), Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) HA)), Φ, hΦover, ?_, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · intro v hv
    let f := (eA.symm ⟨v, hv⟩).ofConv
    refine ⟨⟨Spec.map (CommRingCat.ofHom f.toRingHom), ?_⟩, ?_⟩
    · rw [← hbase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, f.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    · show Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Φ = _
      rw [hread f]
      simp [f]
  · intro x

    let f₀ : HA →+* AlgebraicClosure ℚ := (Spec.preimage x.1).hom
    have hf₀ : f₀.comp (algebraMap ↥(shRing A) HA) = algebraMap ↥(shRing A) (AlgebraicClosure ℚ) := by
      have h1 : Spec.map (CommRingCat.ofHom (f₀.comp (algebraMap ↥(shRing A) HA))) =
          Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) := by
        rw [hbase, ← x.2, CommRingCat.ofHom_comp, Spec.map_comp]
        congr 1
        show Spec.map (CommRingCat.ofHom (Spec.preimage x.1).hom) = x.1
        rw [CommRingCat.ofHom_hom, Spec.map_preimage]
      have h2 := Spec.map_injective h1
      exact congrArg CommRingCat.Hom.hom h2
    let f : HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ := { f₀ with commutes' := fun r => RingHom.congr_fun hf₀ r }
    refine ⟨((eA (WithConv.toConv f) : ↥V) : JZero (N₀ * p)), (eA (WithConv.toConv f)).2, ?_⟩
    have hx : x.1 = Spec.map (CommRingCat.ofHom f.toRingHom) := by
      show x.1 = Spec.map (CommRingCat.ofHom f₀)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [hx, hread f]

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_isFinite_forall_ptsN_comp_eq_of_hopf
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_isFinite_forall_ptsN_comp_eq_of_hopf (solution)
