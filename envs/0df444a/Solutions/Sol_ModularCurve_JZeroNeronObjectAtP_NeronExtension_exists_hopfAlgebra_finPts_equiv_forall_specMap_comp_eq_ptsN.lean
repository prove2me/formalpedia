-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6562d727-8479-52fa-870b-6c7c32882509

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_mem_finPts_iff
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero PresheafOfModules.ExteriorPower.instModulePresheafAb ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.DRModelPackage.LegTwoInput.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace FINPART

section Generic

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem castOver_injective {B T Y : Scheme.{0}} {ι ι' : T ⟶ B} {g : Y ⟶ B} (h : ι = ι') :
    Function.Injective (castOver (f := g) h) := by
  intro a b hab
  apply Subtype.ext
  have h1 := congrArg Subtype.val hab
  exact h1

theorem castOver_mul {T : Scheme.{0}} {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι')
    (a b : SchemeHomOver ι f) : castOver h (L.mul ι a b) = L.mul ι' (castOver h a) (castOver h b) := by
  subst h; rfl

theorem castOver_one {T : Scheme.{0}} {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') :
    castOver h (L.one ι) = L.one ι' := by
  subst h; rfl

theorem castOver_nsmul {T : Scheme.{0}} {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (n : ℕ)
    (a : SchemeHomOver ι f) : castOver h (L.nsmul ι n a) = L.nsmul ι' n (castOver h a) := by
  subst h; rfl

theorem comp_schemeNsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]
  rfl

abbrev kerIncl (n : ℕ) : L.schemeKer n ⟶ X :=
  pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1

theorem kerIncl_comp (n : ℕ) : kerIncl L n ≫ f = L.schemeKerStr n := by
  have h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  calc kerIncl L n ≫ f = kerIncl L n ≫ L.schemeNsmul n ≫ f := by rw [L.schemeNsmul_over]
    _ = (pullback.snd _ _ ≫ (L.one (𝟙 _)).1) ≫ f := by rw [← Category.assoc, pullback.condition]
    _ = L.schemeKerStr n := by rw [Category.assoc, h1, Category.comp_id]

def kerLift {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ} (x : SchemeHomOver t f)
    (hx : L.IsTorsionPoint t n x) : T ⟶ L.schemeKer n :=
  pullback.lift x.1 t (by rw [comp_schemeNsmul, hx, one_coe])

theorem kerLift_comp_kerIncl {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ} (x : SchemeHomOver t f)
    (hx : L.IsTorsionPoint t n x) : kerLift L x hx ≫ kerIncl L n = x.1 :=
  pullback.lift_fst _ _ _

theorem kerLift_comp_schemeKerStr {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (x : SchemeHomOver t f) (hx : L.IsTorsionPoint t n x) : kerLift L x hx ≫ L.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

theorem isClosedImmersion_kerIncl [IsSeparated f] (n : ℕ) : IsClosedImmersion (kerIncl L n) := by
  have h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  haveI : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
      rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp _ f
  show IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
  infer_instance

end Generic

section Sh

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem subtype_comp_shToPlace :
    A.subtype.comp (shToPlace A) =
      (algebraMap ↥(invField A) (AlgebraicClosure ℚ)).comp (algebraMap ↥(shRing A) ↥(invField A)) := by
  ext x; rfl

theorem barPt_comp_shPt :
    barPt A ≫ shPt A = Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) := by
  show Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (shToPlace A)) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_shToPlace]

theorem specMap_comp_barPt_shPt_of_forall (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hτ : ∀ k : ↥(invField A), τ (k : AlgebraicClosure ℚ) = k) :
    Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A ≫ shPt A =
      barPt A ≫ shPt A := by
  have h : (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap ↥(invField A) (AlgebraicClosure ℚ)) =
      algebraMap ↥(invField A) (AlgebraicClosure ℚ) := by
    ext k; exact hτ k
  rw [barPt_comp_shPt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

variable [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]

theorem algebraMap_sh_eq : algebraMap ↥(shRing A) (AlgebraicClosure ℚ) = A.subtype.comp (shToPlace A) := by
  rw [subtype_comp_shToPlace, ← IsScalarTower.algebraMap_eq]

theorem specMap_algebraMap_sh :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) = barPt A ≫ shPt A := by
  rw [algebraMap_sh_eq, CommRingCat.ofHom_comp, Spec.map_comp]

end Sh

section Pts

theorem nsmul_eq_zero_of_mem_jZeroTorsion {M : ℕ} [NeZero M] {m : ℕ} {x : JZero M}
    (hx : x ∈ jZeroTorsion M m) : m • x = 0 := by
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul] at hx
  exact hx

theorem mem_jZeroTorsion_of_nsmul_eq_zero {M : ℕ} [NeZero M] {m : ℕ} {x : JZero M}
    (hx : m • x = 0) : x ∈ jZeroTorsion M m := by
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul]
  exact hx

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
  {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)

theorem shGenLift_mul (a b : SchemeHomOver (genPt p) O.g) :
    Λ.shGenLift (O.L.mul _ a b) =
      (O.L.baseChange Λ.shStr).mul _ (Λ.shGenLift a) (Λ.shGenLift b) := by
  unfold LevelData.shGenLift
  rw [castOver_mul, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
    RelativeGroupLaw.baseChangePointToBase_ofBase]

theorem ptsN_add (x y : JZero (N₀ * p)) :
    F.ptsN (x + y) = F.LN.mul _ (F.ptsN x) (F.ptsN y) := by
  show NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x + y))) F.openImm = _
  rw [O.pts_add, shGenLift_mul, F.openImm_mul]

theorem ptsN_zero : F.ptsN 0 = F.LN.one _ := by
  letI := F.LN.pointGroup (barPt A ≫ shPt A)
  have h : F.ptsN (0 + 0) = F.ptsN 0 * F.ptsN 0 := ptsN_add F 0 0
  rw [add_zero] at h
  have h' := (congrArg (· * (F.ptsN 0)⁻¹) h).symm
  simp at h'
  exact h'

theorem ptsN_nsmul (n : ℕ) (x : JZero (N₀ * p)) : F.ptsN (n • x) = F.LN.nsmul _ n (F.ptsN x) := by
  induction n with
  | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]; exact ptsN_zero F
  | succ n ih => rw [succ_nsmul, ptsN_add, ih, RelativeGroupLaw.nsmul_succ]

theorem ptsN_injective : Function.Injective F.ptsN := by
  intro x y h
  haveI := F.openImm_isOpenImmersion
  have h1 : (Λ.shGenLift (O.pts x)).1 ≫ F.openImm.1 = (Λ.shGenLift (O.pts y)).1 ≫ F.openImm.1 :=
    congrArg Subtype.val h
  have h2 : (Λ.shGenLift (O.pts x)).1 = (Λ.shGenLift (O.pts y)).1 := (cancel_mono F.openImm.1).mp h1
  have h3 : (O.pts x).1 = (O.pts y).1 := by
    have := congrArg (· ≫ pullback.fst O.g Λ.shStr) h2
    simpa only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase, castOver, pullback.lift_fst] using this
  exact O.pts.injective (Subtype.ext h3)

theorem ptsN_galois (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hτ : ∀ k : ↥(invField A), τ (k : AlgebraicClosure ℚ) = k) (x : JZero (N₀ * p)) :
    (F.ptsN (τ • x)).1 =
      Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (F.ptsN x).1 := by
  have hlift : Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      (Λ.shGenLift (O.pts x)).1 = (Λ.shGenLift (O.pts (τ • x))).1 := by
    simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase, castOver]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (O.pts_galois τ x).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact specMap_comp_barPt_shPt_of_forall A τ hτ
  show (Λ.shGenLift (O.pts (τ • x))).1 ≫ F.openImm.1 = _ ≫ (Λ.shGenLift (O.pts x)).1 ≫ F.openImm.1
  rw [← Category.assoc, hlift]

end Pts

namespace Ext

section plumbing

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem subtype_comp_shToPlace :
    A.subtype.comp (shToPlace A) =
      (algebraMap ↥(invField A) (AlgebraicClosure ℚ)).comp (algebraMap ↥(shRing A) ↥(invField A)) := by
  ext x; rfl

theorem algebraMap_sh_eq [Algebra ↥(shRing A) (AlgebraicClosure ℚ)]
    [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)] :
    algebraMap ↥(shRing A) (AlgebraicClosure ℚ) = A.subtype.comp (shToPlace A) := by
  rw [IsScalarTower.algebraMap_eq ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ), subtype_comp_shToPlace]

theorem algebraMap_place_eq : algebraMap ↥A (AlgebraicClosure ℚ) = A.subtype := RingHom.ext fun _ => rfl

end plumbing

theorem extN_of_algHom
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
    {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    {H : Type} [CommRing H] [Algebra ↥(shRing A) H] [Module.Finite ↥(shRing A) H]
    (ι : Spec (CommRingCat.of H) ⟶ F.Nfull)
    (hι : ι ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H)))
    (φ : H →ₐ[↥(shRing A)] AlgebraicClosure ℚ) (x : JZero (N₀ * p))
    (hx : (F.ptsN x).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι) :
    F.ExtN x := by

  letI : Algebra ↥(shRing A) ↥A := (shToPlace A).toAlgebra
  haveI : IsScalarTower ↥(shRing A) ↥A (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' (by rw [algebraMap_sh_eq, algebraMap_place_eq]; rfl)

  have hmem : ∀ h : H, φ h ∈ A := by
    intro h
    have hO : IsIntegral ↥(shRing A) (φ h) := (Algebra.IsIntegral.isIntegral (R := ↥(shRing A)) h).map φ
    have hA' : IsIntegral ↥A (φ h) := hO.tower_top
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hA'
    rw [← ha, algebraMap_place_eq]
    exact a.2

  let fA : H →+* ↥A := φ.toRingHom.codRestrict A.toSubring hmem
  have h1 : A.subtype.comp fA = φ.toRingHom := RingHom.ext fun _ => rfl
  have h2 : fA.comp (algebraMap ↥(shRing A) H) = shToPlace A := by
    ext r
    show φ (algebraMap ↥(shRing A) H r) = ((shToPlace A r : ↥A) : AlgebraicClosure ℚ)
    rw [φ.commutes, algebraMap_sh_eq]
    rfl
  refine ⟨⟨Spec.map (CommRingCat.ofHom fA) ≫ ι, ?_⟩, ?_⟩
  ·
    show (Spec.map (CommRingCat.ofHom fA) ≫ ι) ≫ F.gN = Spec.map (CommRingCat.ofHom (shToPlace A))
    rw [Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h2]
  ·
    show (F.ptsN x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom fA) ≫ ι
    rw [hx, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h1]

end Ext

section Surj

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
  {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)

set_option maxHeartbeats 16000000 in

theorem exists_algHom_of_extN
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    [IsSeparated F.gN] (m : ℕ) {H : Type} [CommRing H] [Algebra ↥(shRing A) H]
    (j : Spec (CommRingCat.of H) ⟶ F.LN.schemeKer m) [IsOpenImmersion j]
    (hj : j ≫ F.LN.schemeKerStr m = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H)))
    (hspecial : ∀ z : ↥(F.LN.schemeKer m),
      (F.LN.schemeKerStr m).base z = IsLocalRing.closedPoint ↥(shRing A) → z ∈ Set.range j.base)
    (x : JZero (N₀ * p)) (hxm : m • x = 0) (hxe : F.ExtN x) :
    ∃ φ : H →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j ≫ kerIncl F.LN m = (F.ptsN x).1 := by
  have hbar : Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) = barPt A ≫ shPt A :=
    specMap_algebraMap_sh A

  have hQt : F.LN.IsTorsionPoint _ m (castOver hbar.symm (F.ptsN x)) := by
    show F.LN.nsmul _ m (castOver hbar.symm (F.ptsN x)) = F.LN.one _
    rw [← castOver_nsmul, ← ptsN_nsmul, hxm, ptsN_zero, castOver_one]
  let y' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ F.LN.schemeKer m := kerLift F.LN _ hQt
  have hy'1 : y' ≫ kerIncl F.LN m = (F.ptsN x).1 := kerLift_comp_kerIncl F.LN _ hQt
  have hy'2 : y' ≫ F.LN.schemeKerStr m =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) :=
    kerLift_comp_schemeKerStr F.LN _ hQt

  let pt : ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))) := IsLocalRing.closedPoint (AlgebraicClosure ℚ)
  have hξ : y'.base pt ∈ Set.range j.base := by
    by_contra hnot
    obtain ⟨z, hz1, hz2⟩ :=
      (NeronExtension.extN_iff_closure_inter_preimage_closedPoint_nonempty F x).mp hxe
    haveI : IsClosedImmersion (kerIncl F.LN m) := isClosedImmersion_kerIncl F.LN m
    have hcm : IsClosedMap (kerIncl F.LN m).base := (kerIncl F.LN m).isClosedEmbedding.isClosedMap
    have hsub : closure {(F.ptsN x).1.base pt} ⊆ (kerIncl F.LN m).base '' closure {y'.base pt} := by
      apply closure_minimal _ (hcm _ isClosed_closure)
      rw [Set.singleton_subset_iff]
      refine ⟨y'.base pt, subset_closure rfl, ?_⟩
      rw [← hy'1]
      rfl
    obtain ⟨z', hz', rfl⟩ := hsub hz1
    have hC : closure {y'.base pt} ⊆ (Set.range j.base)ᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr hnot) (IsOpenImmersion.isOpen_range j).isClosed_compl
    apply hC hz'
    apply hspecial
    have hz3 : (kerIncl F.LN m ≫ F.gN).base z' = IsLocalRing.closedPoint ↥(shRing A) := hz2
    rwa [kerIncl_comp] at hz3
  have hrange : Set.range y'.base ⊆ Set.range j.base := by
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = pt := Subsingleton.elim _ _
    exact hξ

  let yt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of H) := IsOpenImmersion.lift j y' hrange
  have hyt : yt ≫ j = y' := IsOpenImmersion.lift_fac j y' hrange
  let φ₀ : H →+* AlgebraicClosure ℚ := (Spec.preimage yt).hom
  have hφ₀ : Spec.map (CommRingCat.ofHom φ₀) = yt := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage yt).hom) = yt
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomm : φ₀.comp (algebraMap ↥(shRing A) H) = algebraMap ↥(shRing A) (AlgebraicClosure ℚ) := by
    have h1 : Spec.map (CommRingCat.ofHom (φ₀.comp (algebraMap ↥(shRing A) H))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ₀, ← hj, ← Category.assoc, hyt, hy'2]
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa only [CommRingCat.hom_ofHom] using h2
  let φ : H →ₐ[↥(shRing A)] AlgebraicClosure ℚ :=
    { toRingHom := φ₀, commutes' := fun r => RingHom.congr_fun hcomm r }
  refine ⟨φ, ?_⟩
  show Spec.map (CommRingCat.ofHom φ₀) ≫ j ≫ kerIncl F.LN m = (F.ptsN x).1
  rw [hφ₀, ← Category.assoc, hyt, hy'1]

end Surj

set_option maxHeartbeats 16000000 in
theorem finpart
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (m : ℕ) (hm : 0 < m) :
    ∃ (H_f : Type) (_ : CommRing H_f) (_ : HopfAlgebra ↥(shRing A) H_f),
      Module.Finite ↥(shRing A) H_f ∧ Module.Flat ↥(shRing A) H_f ∧ Coalgebra.IsCocomm ↥(shRing A) H_f ∧
      ∃ (ι : Spec (CommRingCat.of H_f) ⟶ F.Nfull)
        (ef : WithConv (H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥(F.finPts m)),
        Module.finrank ↥(shRing A) H_f = Nat.card ↥(F.finPts m) ∧
        ι ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H_f)) ∧
        (∀ (C : Type) [CommRing C] [Algebra ↥(shRing A) C] (φ ψ : H_f →ₐ[↥(shRing A)] C)
            (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) C))) F.gN),
          x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι →
          y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι →
          (F.LN.mul _ x y).1 =
            Spec.map (CommRingCat.ofHom
              (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ ι) ∧
        (∀ f g, ((ef (f * g) : ↥(F.finPts m)) : JZero (N₀ * p)) = ef f + ef g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
            (f g : WithConv (H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
          (∀ h : H_f, g h = σ (f h)) →
            ((ef g : ↥(F.finPts m)) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((ef f : ↥(F.finPts m)) : JZero (N₀ * p))) ∧
        (∀ f : H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ι = (F.ptsN ((ef (WithConv.toConv f) : ↥(F.finPts m)) : JZero (N₀ * p))).1) := by
  classical

  haveI hDVR : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  haveI : IsDedekindDomain ↥(shRing A) := inferInstance
  haveI : HenselianLocalRing ↥(shRing A) :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
  haveI : IsSeparated F.gN := F.hN.separated
  haveI : LocallyOfFiniteType F.gN := F.hN.locallyOfFiniteType

  obtain ⟨hlqf, hqc, hfl⟩ :=
    NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul N₀ p hpN₀ A hA Λ hΛ O F m hm
  haveI := hlqf; haveI := hqc; haveI := hfl
  haveI : LocallyQuasiFinite (F.LN.schemeKerStr m) := by delta RelativeGroupLaw.schemeKerStr; infer_instance
  haveI : QuasiCompact (F.LN.schemeKerStr m) := by delta RelativeGroupLaw.schemeKerStr; infer_instance
  haveI : Flat (F.LN.schemeKerStr m) := by delta RelativeGroupLaw.schemeKerStr; infer_instance

  obtain ⟨H, _i1, _i2, hfin, hflat, hcocomm, j, e, hj, hjo, hjc, hspecial, he1, heinj, hesurj, hemul, henat⟩ :=
    RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing F.LN
      (fun t x y => F.commN t x y) m
  haveI := hjo; haveI := hjc; haveI := hfin
  let ι : Spec (CommRingCat.of H) ⟶ F.Nfull := j ≫ kerIncl F.LN m
  have hι : ι ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H)) := by
    show (j ≫ kerIncl F.LN m) ≫ F.gN = _
    rw [Category.assoc, kerIncl_comp, hj]
  have hbar : Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) (AlgebraicClosure ℚ))) = barPt A ≫ shPt A :=
    specMap_algebraMap_sh A

  let P : WithConv (H →ₐ[↥(shRing A)] AlgebraicClosure ℚ) → SchemeHomOver (barPt A ≫ shPt A) F.gN :=
    fun f => castOver hbar (e _ f).val
  have hP1 : ∀ f, (P f).1 = Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫ ι := fun f => by
    show (e _ f).val.1 = _ ≫ j ≫ kerIncl F.LN m
    exact he1 _ f
  have hPmul : ∀ f g, P (f * g) = F.LN.mul _ (P f) (P g) := fun f g => by
    show castOver hbar (e _ (f * g)).val = _
    rw [hemul, castOver_mul]
  have hPinj : Function.Injective P := fun f g hfg =>
    heinj _ (Subtype.ext (castOver_injective hbar hfg))
  have hPtors : ∀ f, F.LN.IsTorsionPoint _ m (P f) := fun f => by
    have h2 : F.LN.nsmul _ m (e _ f).val = F.LN.one _ := (e _ f).2
    show F.LN.nsmul _ m (castOver hbar (e _ f).val) = F.LN.one _
    rw [← castOver_nsmul, h2, castOver_one]
  let xf : WithConv (H →ₐ[↥(shRing A)] AlgebraicClosure ℚ) → JZero (N₀ * p) :=
    fun f => Classical.choose (F.openImm_pts_surjective (P f))
  have hxf : ∀ f, F.ptsN (xf f) = P f := fun f => Classical.choose_spec (F.openImm_pts_surjective (P f))
  have hxf_inj : Function.Injective xf := fun f g hfg => hPinj (by rw [← hxf, ← hxf, hfg])
  have hxf_mul : ∀ f g, xf (f * g) = xf f + xf g := fun f g =>
    ptsN_injective F (by rw [ptsN_add, hxf, hxf, hxf, hPmul])

  have hxf_tors : ∀ f, xf f ∈ jZeroTorsion (N₀ * p) m := fun f => by
    apply mem_jZeroTorsion_of_nsmul_eq_zero
    apply ptsN_injective F
    rw [ptsN_nsmul, hxf, ptsN_zero]
    exact hPtors f

  have hxf_ext : ∀ f, F.ExtN (xf f) := fun f =>
    Ext.extN_of_algHom F ι hι f.ofConv (xf f) (by rw [hxf]; exact hP1 f)
  have hxf_mem : ∀ f, xf f ∈ F.finPts m := fun f =>
    (NeronExtension.mem_finPts_iff F m (xf f)).mpr ⟨hxf_tors f, hxf_ext f⟩
  let fwd : WithConv (H →ₐ[↥(shRing A)] AlgebraicClosure ℚ) → ↥(F.finPts m) := fun f => ⟨xf f, hxf_mem f⟩
  have hfwd_inj : Function.Injective fwd := fun f g hfg => hxf_inj (congrArg Subtype.val hfg)

  have hfwd_surj : Function.Surjective fwd := by
    rintro ⟨x, hx⟩
    obtain ⟨hxm, hxe⟩ := (NeronExtension.mem_finPts_iff F m x).mp hx
    obtain ⟨φ, hφ⟩ := exists_algHom_of_extN F m j hj hspecial x (nsmul_eq_zero_of_mem_jZeroTorsion hxm) hxe
    refine ⟨WithConv.toConv φ, Subtype.ext ?_⟩
    show xf (WithConv.toConv φ) = x
    apply ptsN_injective F
    rw [hxf]
    apply Subtype.ext
    rw [hP1, ← hφ]
  let ef : WithConv (H →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥(F.finPts m) := Equiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩
  have hef : ∀ f, ((ef f : ↥(F.finPts m)) : JZero (N₀ * p)) = xf f := fun f => rfl
  refine ⟨H, _i1, _i2, hfin, hflat, hcocomm, ι, ef, ?_, hι, ?_, ?_, ?_, ?_⟩
  ·
    haveI : Module.Free ↥(shRing A) H := Module.free_of_flat_of_isLocalRing
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ↥(shRing A) H (AlgebraicClosure ℚ),
      ← Nat.card_congr ef, Nat.card_congr (WithConv.equiv _)]
  ·
    intro C _ _ φ ψ x y hx hy
    have hx' : x = (e C (WithConv.toConv φ)).val := Subtype.ext (by rw [hx, he1])
    have hy' : y = (e C (WithConv.toConv ψ)).val := Subtype.ext (by rw [hy, he1])
    rw [hx', hy', ← hemul, he1]
  ·
    intro f g
    rw [hef, hef, hef]
    exact hxf_mul f g
  ·
    intro σ f g hfg
    rw [hef, hef]
    apply ptsN_injective F
    apply Subtype.ext
    have hτ : ∀ k : ↥(invField A), (σ.restrictScalars ℚ) (k : AlgebraicClosure ℚ) = k := fun k => σ.commutes k
    have hfg' : g.ofConv.toRingHom =
        ((σ.restrictScalars ℚ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp f.ofConv.toRingHom := by
      ext h; exact hfg h
    rw [ptsN_galois F (σ.restrictScalars ℚ) hτ, hxf, hxf, hP1, hP1, hfg', CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]
  ·
    intro f
    rw [hef, hxf, hP1]

end FINPART

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension)
    [Algebra ↥(shRing A) (AlgebraicClosure ℚ)] [IsScalarTower ↥(shRing A) ↥(invField A) (AlgebraicClosure ℚ)]
    (m : ℕ) (hm : 0 < m) :
    ∃ (H_f : Type) (_ : CommRing H_f) (_ : HopfAlgebra ↥(shRing A) H_f),
      Module.Finite ↥(shRing A) H_f ∧ Module.Flat ↥(shRing A) H_f ∧ Coalgebra.IsCocomm ↥(shRing A) H_f ∧
      ∃ (ι : Spec (CommRingCat.of H_f) ⟶ F.Nfull)
        (ef : WithConv (H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ) ≃ ↥(F.finPts m)),
        Module.finrank ↥(shRing A) H_f = Nat.card ↥(F.finPts m) ∧
        ι ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) H_f)) ∧
        (∀ (C : Type) [CommRing C] [Algebra ↥(shRing A) C] (φ ψ : H_f →ₐ[↥(shRing A)] C)
            (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) C))) F.gN),
          x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι →
          y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι →
          (F.LN.mul _ x y).1 =
            Spec.map (CommRingCat.ofHom
              (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ ι) ∧
        (∀ f g, ((ef (f * g) : ↥(F.finPts m)) : JZero (N₀ * p)) = ef f + ef g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[↥(invField A)] AlgebraicClosure ℚ)
            (f g : WithConv (H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ)),
          (∀ h : H_f, g h = σ (f h)) →
            ((ef g : ↥(F.finPts m)) : JZero (N₀ * p)) = (σ.restrictScalars ℚ) • ((ef f : ↥(F.finPts m)) : JZero (N₀ * p))) ∧
        (∀ f : H_f →ₐ[↥(shRing A)] AlgebraicClosure ℚ,
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ι = (F.ptsN ((ef (WithConv.toConv f) : ↥(F.finPts m)) : JZero (N₀ * p))).1) :=
  FINPART.finpart N₀ p hpN₀ A hA Λ hΛ O F m hm

end
end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hopfAlgebra_finPts_equiv_forall_specMap_comp_eq_ptsN (solution)
