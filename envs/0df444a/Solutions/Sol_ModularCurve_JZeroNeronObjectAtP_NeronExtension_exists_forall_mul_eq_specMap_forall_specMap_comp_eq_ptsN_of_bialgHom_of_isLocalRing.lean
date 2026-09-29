-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e6f5c366-8a0c-59e2-9e8d-123673ec215e

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN
import Theorems.Thm_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_finPts_le_finPts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing
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

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace UProlongS17

theorem exists_natCard_eq_prime_pow (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G] [Finite G]
    (h : ∀ g : G, p • g = 0) : ∃ n : ℕ, Nat.card G = p ^ n := by
  have hG : IsPGroup p (Multiplicative G) := fun g =>
    ⟨1, by rw [pow_one, ← ofAdd_toAdd g, ← ofAdd_nsmul, h, ofAdd_zero]⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  exact ⟨n, hn⟩

section SubgroupAction

variable {M : Type*} [AddCommGroup M]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (V : AddSubgroup M)

@[reducible] noncomputable def subgroupAction
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : M), v ∈ V → (σ.restrictScalars ℚ) • v ∈ V) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) ↥V where
  smul σ v := ⟨(σ.restrictScalars ℚ) • (v : M), hV σ v v.2⟩
  one_smul v := by
    apply Subtype.ext
    change ((1 : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ).restrictScalars ℚ) • (v : M) = v
    rw [show (1 : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ).restrictScalars ℚ = 1 from
      AlgEquiv.ext fun _ => rfl, one_smul]
  mul_smul σ τ v := by
    apply Subtype.ext
    change ((σ * τ).restrictScalars ℚ) • (v : M) = (σ.restrictScalars ℚ) • ((τ.restrictScalars ℚ) • (v : M))
    rw [show (σ * τ).restrictScalars ℚ = σ.restrictScalars ℚ * τ.restrictScalars ℚ from
      AlgEquiv.ext fun _ => rfl, mul_smul]
  smul_zero σ := Subtype.ext (smul_zero (σ.restrictScalars ℚ))
  smul_add σ v w := Subtype.ext (smul_add (σ.restrictScalars ℚ) (v : M) (w : M))

theorem subgroupAction_coe_smul
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : M), v ∈ V → (σ.restrictScalars ℚ) • v ∈ V)
    (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : ↥V) :
    letI := subgroupAction K V hV
    ((σ • v : ↥V) : M) = (σ.restrictScalars ℚ) • (v : M) := rfl

end SubgroupAction

section PointsAction

variable (R K L : Type) [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] (H : Type) [CommRing H] [Bialgebra R H]

def galTwist (σ : L ≃ₐ[K] L) (f : WithConv (H →ₐ[R] L)) : WithConv (H →ₐ[R] L) :=
  WithConv.toConv (((σ : L →ₐ[K] L).restrictScalars R).comp f.ofConv)

variable {R K L H}

theorem galTwist_apply (σ : L ≃ₐ[K] L) (f : WithConv (H →ₐ[R] L)) (x : H) :
    galTwist R K L H σ f x = σ (f x) := rfl

theorem galTwist_one (f : WithConv (H →ₐ[R] L)) : galTwist R K L H 1 f = f :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

theorem galTwist_mul (σ τ : L ≃ₐ[K] L) (f : WithConv (H →ₐ[R] L)) :
    galTwist R K L H (σ * τ) f = galTwist R K L H σ (galTwist R K L H τ f) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

theorem galTwist_convOne (σ : L ≃ₐ[K] L) : galTwist R K L H σ 1 = 1 :=
  WithConv.ext (AlgHom.ext fun x => ((σ : L →ₐ[K] L).restrictScalars R).commutes (Coalgebra.counit x))

theorem galTwist_convMul (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)) :
    galTwist R K L H σ (f * g) = galTwist R K L H σ f * galTwist R K L H σ g := by
  unfold galTwist
  rw [AlgHom.comp_convMul_distrib]

scoped instance ptsAction : DistribMulAction (L ≃ₐ[K] L) (Additive (WithConv (H →ₐ[R] L))) where
  smul σ x := Additive.ofMul (galTwist R K L H σ (Additive.toMul x))
  one_smul x := congrArg Additive.ofMul (galTwist_one (Additive.toMul x))
  mul_smul σ τ x := congrArg Additive.ofMul (galTwist_mul σ τ (Additive.toMul x))
  smul_zero σ := congrArg Additive.ofMul (galTwist_convOne (R := R) (H := H) σ)
  smul_add σ x y := congrArg Additive.ofMul (galTwist_convMul σ (Additive.toMul x) (Additive.toMul y))

theorem ptsAction_smul_def (σ : L ≃ₐ[K] L) (x : Additive (WithConv (H →ₐ[R] L))) :
    σ • x = Additive.ofMul (galTwist R K L H σ (Additive.toMul x)) := rfl

end PointsAction

end UProlongS17
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

open UProlongS17

namespace UProlongS17

section Pullback

variable {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
  {H H₀ : Type} [CommRing H] [CommRing H₀] [Bialgebra R H] [Bialgebra R H₀]
  {M : Type*} [AddCommGroup M]

noncomputable def pullbackHom (π : H →ₐc[R] H₀) (e : WithConv (H →ₐ[R] L) → M) (he : ∀ f g, e (f * g) = e f + e g) :
    Additive (WithConv (H₀ →ₐ[R] L)) →+ M :=
  AddMonoidHom.mk'
    (fun x => e (WithConv.toConv ((WithConv.ofConv (Additive.toMul x)).comp (π : H →ₐ[R] H₀))))
    (fun x y => by
      try dsimp only
      rw [toMul_add, AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv, he])

theorem pullbackHom_apply (π : H →ₐc[R] H₀) (e : WithConv (H →ₐ[R] L) → M)
    (he : ∀ f g, e (f * g) = e f + e g) (x : Additive (WithConv (H₀ →ₐ[R] L))) :
    pullbackHom π e he x = e (WithConv.toConv ((WithConv.ofConv (Additive.toMul x)).comp (π : H →ₐ[R] H₀))) :=
  rfl

end Pullback
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

section FinPts

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
  {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ}

theorem finPts_le_jZeroTorsion (F : O.NeronExtension) (m : ℕ) :
    F.finPts m ≤ jZeroTorsion (N₀ * p) m := by
  unfold NeronExtension.finPts
  exact (AddSubgroup.closure_le _).mpr fun _ hx => hx.1

theorem nsmul_eq_zero_of_mem_jZeroTorsion {M : ℕ} [NeZero M] {m : ℕ} {x : JZero M}
    (hx : x ∈ jZeroTorsion M m) : m • x = 0 := by
  simpa only [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul] using hx

end FinPts
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

end UProlongS17
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

namespace UProlongS17

section PointsGroup

variable (R : Type) [CommRing R] (A : Type) [CommRing A] [HopfAlgebra R A]
  (L : Type) [CommRing L] [Algebra R L]

noncomputable def antipodeAlgHom : A →ₐ[R] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

variable {R A L}

theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom R A a = HopfAlgebra.antipode R a := rfl

theorem convMul_apply_eq_sum (f g : WithConv (A →ₐ[R] L)) {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  change ((WithConv.toConv f.ofConv.toLinearMap * WithConv.toConv g.ofConv.toLinearMap :
    WithConv (A →ₗ[R] L))) a = _
  rw [𝓡.convMul_apply]
  rfl

theorem antipode_convMul_cancel (f : WithConv (A →ₐ[R] L)) :
    WithConv.toConv (f.ofConv.comp (antipodeAlgHom R A)) * f = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  change (WithConv.toConv (f.ofConv.comp (antipodeAlgHom R A)) * f) a = (1 : WithConv (A →ₐ[R] L)) a
  rw [convMul_apply_eq_sum _ _ (Coalgebra.Repr.arbitrary R a), AlgHom.convOne_apply]
  change ∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
      f.ofConv (HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).left i)) *
        f.ofConv ((Coalgebra.Repr.arbitrary R a).right i) = _
  simp_rw [← map_mul, ← map_sum]
  rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]

noncomputable scoped instance instCommGroupPts [Coalgebra.IsCocomm R A] : CommGroup (WithConv (A →ₐ[R] L)) :=
  { (inferInstance : CommMonoid (WithConv (A →ₐ[R] L))) with
    inv := fun f => WithConv.toConv (f.ofConv.comp (antipodeAlgHom R A))
    inv_mul_cancel := fun f => antipode_convMul_cancel f }

end PointsGroup
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

end UProlongS17
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

namespace UProlongS17

section Quotients

variable {G : Type*} [AddCommGroup G]

theorem exists_natCard_quotient_eq_prime_pow (p : ℕ) [Fact p.Prime] [Finite G]
    (hG : ∀ g : G, p • g = 0) (W : AddSubgroup G) : ∃ b : ℕ, Nat.card (G ⧸ W) = p ^ b := by
  haveI : Finite (G ⧸ W) := Finite.of_surjective _ (QuotientAddGroup.mk'_surjective W)
  refine exists_natCard_eq_prime_pow p (G ⧸ W) fun u => ?_
  induction u using QuotientAddGroup.induction_on with
  | H v => rw [← QuotientAddGroup.mk_nsmul, hG, QuotientAddGroup.mk_zero]

theorem mk'_addSubgroupOf_eq_iff (S V : AddSubgroup G) (x y : ↥V) :
    QuotientAddGroup.mk' (S.addSubgroupOf V) x = QuotientAddGroup.mk' (S.addSubgroupOf V) y ↔
      (x : G) - (y : G) ∈ S := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub]

theorem mk'_addSubgroupOf_eq_zero_iff (S V : AddSubgroup G) (x : ↥V) :
    QuotientAddGroup.mk' (S.addSubgroupOf V) x = 0 ↔ (x : G) ∈ S := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

end Quotients
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

section Generic

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  (p : ℕ) [Fact p.Prime]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [Algebra R ↥K] [IsFractionRing R ↥K]
  [Algebra R (AlgebraicClosure ℚ)] [IsScalarTower R ↥K (AlgebraicClosure ℚ)]
  {J : Type} [AddCommGroup J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]

omit [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] [IsFractionRing R ↥K] in

theorem smul_mem_of_equiv (V : AddSubgroup J) (H : Type) [CommRing H] [Bialgebra R H]
    (e : WithConv (H →ₐ[R] AlgebraicClosure ℚ) ≃ ↥V)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥V) : J) = (σ.restrictScalars ℚ) • ((e f : ↥V) : J))
    (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : J) (hv : v ∈ V) :
    (σ.restrictScalars ℚ) • v ∈ V := by
  have h := he_act σ (e.symm ⟨v, hv⟩)
    (galTwist R ↥K (AlgebraicClosure ℚ) H σ (e.symm ⟨v, hv⟩)) (fun _ => rfl)
  rw [Equiv.apply_symm_apply] at h
  have h' : (σ.restrictScalars ℚ) • v = _ := h.symm
  rw [h']
  exact (e _).2

theorem coe_apply_mem_of_forall_smul_sub_mem (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (V S : AddSubgroup J) [Finite ↥V] (hVp : ∀ v : ↥V, p • v = 0)
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H] (hrank : ∃ a : ℕ, Module.finrank R H = p ^ a)
    (e : WithConv (H →ₐ[R] AlgebraicClosure ℚ) ≃ ↥V)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥V) : J) = (σ.restrictScalars ℚ) • ((e f : ↥V) : J))
    (H₀ : Type) [CommRing H₀] [Bialgebra R H₀] (hloc : IsLocalRing H₀) (π : H →ₐc[R] H₀)
    (hS : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : J), v ∈ V →
      (σ.restrictScalars ℚ) • v - v ∈ S)
    (f₀ : H₀ →ₐ[R] AlgebraicClosure ℚ) :
    ((e (WithConv.toConv (f₀.comp (π : H →ₐ[R] H₀))) : ↥V) : J) ∈ S := by
  letI := subgroupAction K V (smul_mem_of_equiv R K V H e he_act)
  have he_act' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f :=
    fun σ f g h => Subtype.ext (he_act σ f g h)
  have hU := exists_natCard_quotient_eq_prime_pow p hVp (S.addSubgroupOf V)
  have hφ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (v : ↥V),
      QuotientAddGroup.mk' (S.addSubgroupOf V) (σ • v) = QuotientAddGroup.mk' (S.addSubgroupOf V) v :=
    fun σ v => (mk'_addSubgroupOf_eq_iff S V _ _).mpr (hS σ v v.2)
  have h0 := HopfAlgebra.apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
    R p hp2 hunif ↥K (AlgebraicClosure ℚ) H hrank e he_add he_act' H₀ hloc π hU
    (QuotientAddGroup.mk' (S.addSubgroupOf V)) hφ f₀
  exact (mk'_addSubgroupOf_eq_zero_iff S V _).mp h0

theorem exists_bialgHom_forall_coe_apply_eq (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (S : AddSubgroup J) [Finite ↥S] (hSp : ∀ x : ↥S, p • x = 0)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Free R H₀]
    [Coalgebra.IsCocomm R H₀] (hrank₀ : ∃ b : ℕ, Module.finrank R H₀ = p ^ b)
    (Hf : Type) [CommRing Hf] [HopfAlgebra R Hf] [Module.Finite R Hf] [Module.Free R Hf]
    [Coalgebra.IsCocomm R Hf] (hrankf : Module.finrank R Hf = Nat.card ↥S)
    (ef : WithConv (Hf →ₐ[R] AlgebraicClosure ℚ) ≃ ↥S)
    (hef_add : ∀ f g, ((ef (f * g) : ↥S) : J) = ef f + ef g)
    (hef_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (Hf →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : Hf, g x = σ (f x)) → ((ef g : ↥S) : J) = (σ.restrictScalars ℚ) • ((ef f : ↥S) : J))
    (ψ : WithConv (H₀ →ₐ[R] AlgebraicClosure ℚ) → J)
    (hψ_mul : ∀ f g, ψ (f * g) = ψ f + ψ g)
    (hψ_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (H₀ →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : H₀, g x = σ (f x)) → ψ g = (σ.restrictScalars ℚ) • ψ f)
    (hψS : ∀ f, ψ f ∈ S) :
    ∃ g : Hf →ₐc[R] H₀, ∀ f₀ : H₀ →ₐ[R] AlgebraicClosure ℚ,
      ((ef (WithConv.toConv (f₀.comp (g : Hf →ₐ[R] H₀))) : ↥S) : J) = ψ (WithConv.toConv f₀) := by
  obtain ⟨b, hb⟩ := exists_natCard_eq_prime_pow p ↥S hSp
  have hrank₂ : ∃ b : ℕ, Module.finrank R Hf = p ^ b := ⟨b, hrankf.trans hb⟩
  letI := subgroupAction K S (smul_mem_of_equiv R K S Hf ef hef_act)
  have hef_add' : ∀ f g, ef (f * g) = ef f + ef g := fun f g => Subtype.ext (hef_add f g)
  have hef_act' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ)
      (f g : WithConv (Hf →ₐ[R] AlgebraicClosure ℚ)),
      (∀ x : Hf, g x = σ (f x)) → ef g = σ • ef f :=
    fun σ f g h => Subtype.ext (hef_act σ f g h)
  let φ : Additive (WithConv (H₀ →ₐ[R] AlgebraicClosure ℚ)) →+ ↥S :=
    (AddMonoidHom.mk' (fun x => ψ (Additive.toMul x)) (fun x y => hψ_mul _ _)).codRestrict S
      (fun x => hψS _)
  have hφ_val : ∀ x, (φ x : J) = ψ (Additive.toMul x) := fun _ => rfl
  have hφ_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) (m), φ (σ • m) = σ • φ m := by
    intro σ m
    apply Subtype.ext
    rw [hφ_val, subgroupAction_coe_smul, hφ_val]
    exact hψ_act σ _ _ (fun _ => rfl)
  obtain ⟨g, hg⟩ :=
    (HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
      R p hp2 hunif ↥K (AlgebraicClosure ℚ)
      H₀ hrank₀ (Additive.ofMul : WithConv (H₀ →ₐ[R] AlgebraicClosure ℚ) ≃ _)
      (fun _ _ => rfl)
      (fun σ f g h => congrArg Additive.ofMul (WithConv.ext (AlgHom.ext h)))
      Hf hrank₂ ef hef_add' hef_act' φ hφ_act).exists
  exact ⟨g, fun f₀ => congrArg Subtype.val (hg (WithConv.toConv f₀))⟩

end Generic
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

end UProlongS17
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

namespace UProlongS17

theorem coe_apply_convMul_comp {R L H H₀ : Type} [CommRing R] [Field L] [Algebra R L]
    [CommRing H] [CommRing H₀] [Bialgebra R H] [Bialgebra R H₀]
    {J : Type*} [AddCommGroup J] (V : AddSubgroup J) (π : H →ₐc[R] H₀)
    (e : WithConv (H →ₐ[R] L) → ↥V) (he_add : ∀ f g, e (f * g) = e f + e g)
    (f g : WithConv (H₀ →ₐ[R] L)) :
    ((e (WithConv.toConv ((f * g).ofConv.comp (π : H →ₐ[R] H₀))) : ↥V) : J) =
      (e (WithConv.toConv (f.ofConv.comp (π : H →ₐ[R] H₀))) : J) +
        (e (WithConv.toConv (g.ofConv.comp (π : H →ₐ[R] H₀))) : J) := by
  rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv, he_add, AddSubgroup.coe_add]

end UProlongS17
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing.UProlongS17"

set_option maxHeartbeats 3200000 in

theorem uprolong_incl
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension)
    (hIU : ∀ (m : ℕ), m.Coprime p →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m)
    (hII : ∀ (m : ℕ), 0 < m →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m)
    (hp2 : p ≠ 2)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (V : AddSubgroup (JZero (N₀ * p))) (hV : V ≤ jZeroTorsion (N₀ * p) p)
    (HA : Type) [CommRing HA] [HopfAlgebra ↥(shRing A) HA]
    [Module.Finite ↥(shRing A) HA] [Module.Free ↥(shRing A) HA] [Coalgebra.IsCocomm ↥(shRing A) HA]
    (hrank : ∃ a : ℕ, Module.finrank ↥(shRing A) HA = p ^ a)
    (eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
      (f g : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
      (∀ h : HA, g h = σ (f h)) →
        ((eA g : ↥V) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : JZero (N₀ * p)))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥(shRing A) H₀] (hloc : IsLocalRing H₀)
    [Module.Finite ↥(shRing A) H₀] [Module.Free ↥(shRing A) H₀] [Coalgebra.IsCocomm ↥(shRing A) H₀]
    (hrank₀ : ∃ b : ℕ, Module.finrank ↥(shRing A) H₀ = p ^ b)
    (π : HA →ₐc[↥(shRing A)] H₀) :
    ∀ f₀ : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
      ((eA (WithConv.toConv (f₀.comp (π : HA →ₐ[↥(shRing A)] H₀))) : ↥V) : JZero (N₀ * p)) ∈ F.finPts p := by

  intro f₀

  obtain ⟨hdvr, hirr, hcz, -⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
  haveI : IsDiscreteValuationRing ↥(shRing A) := hdvr
  haveI : CharZero ↥(shRing A) := hcz
  have hp : (p : ℕ).Prime := Fact.out

  have hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ,
      σ.restrictScalars ℚ ∈ A.inertiaSubgroupIn ℚ := by
    intro σ
    obtain ⟨Osub, -, -, -, -, -, hiff, -⟩ :=
      ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p A hA
    refine (hiff (σ.restrictScalars ℚ)).mpr fun x hx => ?_
    have hxK : x ∈ invField A := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (hiff τ).mp hτ x hx
    exact σ.commutes (⟨x, hxK⟩ : ↥(invField A))

  obtain ⟨a, ha⟩ := hrank
  have hcardV : Nat.card ↥V = p ^ a := by
    rw [← ha, ← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ↥(shRing A) HA (AlgebraicClosure ℚ)]
    exact (Nat.card_congr eA).symm.trans (Nat.card_congr (WithConv.equiv _))
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp.ne_zero)
  have hVp : ∀ v : ↥V, p • v = 0 := fun v =>
    Subtype.ext (nsmul_eq_zero_of_mem_jZeroTorsion (hV v.2))

  exact coe_apply_mem_of_forall_smul_sub_mem ↥(shRing A) p (invField A) hp2 hirr V (F.finPts p) hVp
    HA ⟨a, ha⟩ eA heA_add heA_act H₀ hloc π
    (fun σ v hv => NeronExtension.finPts_le_finPts F p (hII p hp.pos _ (hinert σ) v (hV hv))) f₀

set_option maxHeartbeats 3200000 in

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
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (V : AddSubgroup (JZero (N₀ * p))) (hV : V ≤ jZeroTorsion (N₀ * p) p)
    (HA : Type) [CommRing HA] [HopfAlgebra ↥(shRing A) HA]
    [Module.Finite ↥(shRing A) HA] [Module.Free ↥(shRing A) HA] [Coalgebra.IsCocomm ↥(shRing A) HA]
    (hrank : ∃ a : ℕ, Module.finrank ↥(shRing A) HA = p ^ a)
    (eA : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥V)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
      (f g : WithConv (HA →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
      (∀ h : HA, g h = σ (f h)) →
        ((eA g : ↥V) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((eA f : ↥V) : JZero (N₀ * p)))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥(shRing A) H₀] (hloc : IsLocalRing H₀)
    [Module.Finite ↥(shRing A) H₀] [Module.Free ↥(shRing A) H₀] [Coalgebra.IsCocomm ↥(shRing A) H₀]
    (hrank₀ : ∃ b : ℕ, Module.finrank ↥(shRing A) H₀ = p ^ b)
    (π : HA →ₐc[↥(shRing A)] H₀) :
    ∃ u : Spec (CommRingCat.of H₀) ⟶ F.Nfull,
      u ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H₀)) ∧

      (∀ (C : Type) [CommRing C] [Algebra ↥(shRing A) C] (φ ψ : H₀ →ₐ[↥(shRing A)] C)
          (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) C))) F.gN),
        x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ u →
        y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u →
        (F.LN.mul _ x y).1 =
          Spec.map (CommRingCat.ofHom
            (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ u) ∧

      (∀ f₀ : H₀ →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
        Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ u =
          (F.ptsN ((eA (WithConv.toConv (f₀.comp (π : HA →ₐ[↥(shRing A)] H₀))) : ↥V) : JZero (N₀ * p))).1) := by

  obtain ⟨hdvr, hirr, hcz, -⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
  haveI : IsDiscreteValuationRing ↥(shRing A) := hdvr
  haveI : CharZero ↥(shRing A) := hcz
  have hp : (p : ℕ).Prime := Fact.out

  have hincl := uprolong_incl N₀ p hpN₀ A hA Λ hΛ O F hIU hII hp2 V hV HA hrank eA heA_add heA_act
    H₀ hloc hrank₀ π

  obtain ⟨Hf, _i1, _i2, hfin, hflat, hcocomm, ι, ef, hrankf, hι, hmulι, hef_add, hef_act, hefpts⟩ :=
    NeronExtension.exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN
      N₀ p hpN₀ A hA Λ hΛ O F p hp.pos
  haveI := hfin
  haveI := hflat
  haveI := hcocomm
  haveI : Module.Free ↥(shRing A) Hf := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial Hf := (Bialgebra.counitAlgHom ↥(shRing A) Hf).toRingHom.domain_nontrivial
  have hfinrank_pos : 0 < Module.finrank ↥(shRing A) Hf :=
    (Module.finrank_pos_iff_of_free ↥(shRing A) Hf).mpr inferInstance
  haveI : Finite ↥(F.finPts p) :=
    Nat.finite_of_card_ne_zero (by rw [← hrankf]; exact hfinrank_pos.ne')
  have hFp : ∀ x : ↥(F.finPts p), p • x = 0 := fun x =>
    Subtype.ext (nsmul_eq_zero_of_mem_jZeroTorsion (finPts_le_jZeroTorsion F p x.2))

  obtain ⟨g, hg⟩ := exists_bialgHom_forall_coe_apply_eq ↥(shRing A) p (invField A) hp2 hirr
    (F.finPts p) hFp H₀ hrank₀ Hf hrankf ef hef_add hef_act
    (fun f => ((eA (WithConv.toConv (f.ofConv.comp (π : HA →ₐ[↥(shRing A)] H₀))) : ↥V) : JZero (N₀ * p)))
    (fun f f' => coe_apply_convMul_comp V π eA heA_add f f')
    (fun σ f f' h => heA_act σ _ _ (fun x => h (π x)))
    (fun f => hincl f.ofConv)

  have ecomp : ∀ {C : Type} [CommRing C] [Algebra ↥(shRing A) C] (χ : H₀ →ₐ[↥(shRing A)] C),
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (g : Hf →ₐ[↥(shRing A)] H₀).toRingHom) =
        Spec.map (CommRingCat.ofHom (χ.comp (g : Hf →ₐ[↥(shRing A)] H₀)).toRingHom) := by
    intro C _ _ χ
    rw [← Spec.map_comp]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom (g : Hf →ₐ[↥(shRing A)] H₀).toRingHom) ≫ ι, ?_, ?_, ?_⟩
  · rw [Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_algebraMap]
  · intro C _ _ φ' ψ' x y hx hy
    rw [← Category.assoc, ecomp] at hx hy
    rw [hmulι C _ _ x y hx hy, ← Category.assoc, ecomp, AlgHom.convMul_comp_bialgHom_distrib]
  · intro f₀
    rw [← Category.assoc, ecomp, hefpts, hg]

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_forall_mul_eq_specMap_forall_specMap_comp_eq_ptsN_of_bialgHom_of_isLocalRing (solution)
