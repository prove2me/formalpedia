-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c97162a7-8bde-5a98-9045-6321ec69e159

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_section_specN_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_mem_range_openImm_of_base_ne_closedPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero PresheafOfModules.ExteriorPower.instModulePresheafAb ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace COVERAsm

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A} {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)

def cst (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} (t : T ⟶ shBase A) : SchemeHomOver t F.gN :=
  ⟨t ≫ σ.1, (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) σ.2).trans (Category.comp_id t))⟩

theorem comp_eq_cst (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} (t : T ⟶ shBase A) (ht : t ≫ 𝟙 _ = t) :
    GoodReductionJacobian.schemeHomOverComp t ht σ = cst F σ t :=
  Subtype.ext rfl

def transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) : F.Nfull ⟶ F.Nfull :=
  (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN)).1

theorem comp_transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} {t : T ⟶ shBase A} (z : SchemeHomOver t F.gN) :
    z.1 ≫ transl F σ = (F.LN.mul t z (cst F σ t)).1 := by
  have key := congrArg Subtype.val (F.LN.mul_natural F.gN t z.1 z.2 ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN))
  have hz : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ : SchemeHomOver F.gN F.gN) = z :=
    Subtype.ext (Category.comp_id _)
  have hc : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (cst F σ F.gN) = cst F σ t :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; show z.1 ≫ F.gN ≫ σ.1 = t ≫ σ.1; rw [← Category.assoc, z.2])
  rw [hz, hc, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

theorem transl_comp_transl (σ τ : SchemeHomOver (𝟙 (shBase A)) F.gN) :
    transl F σ ≫ transl F τ = transl F (F.LN.mul (𝟙 _) σ τ) := by
  have h1 : transl F σ ≫ transl F τ = (F.LN.mul F.gN (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN)) (cst F τ F.gN)).1 :=
    comp_transl F τ _
  have h2 : cst F (F.LN.mul (𝟙 _) σ τ) F.gN = F.LN.mul F.gN (cst F σ F.gN) (cst F τ F.gN) := by
    have := F.LN.mul_natural (𝟙 _) F.gN F.gN (Category.comp_id _) σ τ
    rw [comp_eq_cst F σ, comp_eq_cst F τ, comp_eq_cst F (F.LN.mul (𝟙 _) σ τ)] at this
    exact this
  rw [h1, transl, h2, F.LN.mul_assoc]

theorem cst_one {T : Scheme.{0}} (t : T ⟶ shBase A) : cst F (F.LN.one (𝟙 _)) t = F.LN.one t := by
  have := GoodReductionJacobian.RelativeGroupLaw.one_natural F.LN (𝟙 _) t t (Category.comp_id _)
  rw [comp_eq_cst F (F.LN.one (𝟙 _))] at this
  exact this

theorem transl_one : transl F (F.LN.one (𝟙 _)) = 𝟙 F.Nfull := by
  rw [transl, cst_one, F.LN.mul_one]

scoped instance isIso_transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) : IsIso (transl F σ) :=
  ⟨⟨transl F (F.LN.inv (𝟙 _) σ), by rw [transl_comp_transl, F.LN.mul_inv_cancel, transl_one],
    by rw [transl_comp_transl, F.LN.inv_mul_cancel, transl_one]⟩⟩

theorem isLocalHom_shToPlace : IsLocalHom (shToPlace A) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : ((x : ↥(invField A)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have : (shToPlace A x : ↥A) = 0 := Subtype.ext (by rw [coe_shToPlace, h]; rfl)
    rw [← hu] at this
    exact u.ne_zero this
  have hx0' : (x : ↥(invField A)) ≠ 0 := fun h => hx0 (by rw [h]; rfl)

  have hmem : (x : ↥(invField A))⁻¹ ∈ shRing A := by
    show algebraMap ↥(invField A) (AlgebraicClosure ℚ) ((x : ↥(invField A))⁻¹) ∈ A
    rw [map_inv₀]
    have hval : algebraMap ↥(invField A) (AlgebraicClosure ℚ) (x : ↥(invField A)) = ((u : ↥A) : AlgebraicClosure ℚ) := by
      rw [hu]; rfl
    rw [hval]
    have : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = (((u : ↥A) : AlgebraicClosure ℚ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have hmul : ((u⁻¹ : (↥A)ˣ) : ↥A) * (u : ↥A) = 1 := Units.inv_mul u
      show ((((u⁻¹ : (↥A)ˣ) : ↥A) * (u : ↥A) : ↥A) : AlgebraicClosure ℚ) = 1
      rw [hmul]; rfl
    rw [← this]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  refine ⟨⟨x, ⟨(x : ↥(invField A))⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0'), Subtype.ext (inv_mul_cancel₀ hx0')⟩, rfl⟩

theorem shPt_base_closedPoint : (shPt A).base (IsLocalRing.closedPoint ↥A) = IsLocalRing.closedPoint ↥(shRing A) := by
  haveI := isLocalHom_shToPlace (A := A)
  exact IsLocalRing.comap_closedPoint (shToPlace A)

end COVERAsm
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul.COVERAsm"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul.COVERAsm"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∃ y : componentGroup O.width → SchemeHomOver (𝟙 (shBase A)) F.gN,

      (∀ φ, F.specN ⟨shPt A ≫ (y φ).1,
          (Category.assoc _ _ _).trans ((congrArg (shPt A ≫ ·) (y φ).2).trans (Category.comp_id _))⟩ = φ) ∧

      (∀ n : ↥F.Nfull, ∃ φ,
        n ∈ Set.range (F.openImm.1 ≫
          (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩
            ⟨F.gN ≫ (y φ).1,
              (Category.assoc _ _ _).trans ((congrArg (F.gN ≫ ·) (y φ).2).trans (Category.comp_id F.gN))⟩).1).base) := by
  classical
  have hsec := fun φ => NeronExtension.exists_section_specN_eq N₀ p hpN₀ A hA Λ hΛ O F φ
  let y : componentGroup O.width → SchemeHomOver (𝟙 (shBase A)) F.gN :=
    fun φ => if φ = 0 then F.LN.one (𝟙 _) else (hsec φ).choose

  have hone : F.specN (F.LN.one (shPt A)) = 0 := by
    have h := F.specN_mul (F.LN.one (shPt A)) (F.LN.one (shPt A))
    rw [F.LN.one_mul] at h
    have h' : F.specN (F.LN.one (shPt A)) + F.specN (F.LN.one (shPt A)) = F.specN (F.LN.one (shPt A)) + 0 := by
      rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hy : ∀ φ, F.specN (COVERAsm.cst F (y φ) (shPt A)) = φ := by
    intro φ
    by_cases h : φ = 0
    · subst h
      simp only [y, if_true]
      rw [COVERAsm.cst_one]
      exact hone
    · simp only [y, if_neg h]
      exact (hsec φ).choose_spec
  refine ⟨y, hy, fun n => ?_⟩
  haveI : IsOpenImmersion F.openImm.1 := F.openImm_isOpenImmersion
  by_cases hn : F.gN.base n = IsLocalRing.closedPoint ↥(shRing A)
  ·
    obtain ⟨n₀, σ, hsp, hσ⟩ :=
      NeronExtension.exists_specializes_section_base_closedPoint_eq N₀ p hpN₀ A hA Λ hΛ O F n hn
    let s : SchemeHomOver (shPt A) F.gN := COVERAsm.cst F σ (shPt A)
    let φ := F.specN s
    let c : SchemeHomOver (shPt A) F.gN := COVERAsm.cst F (y φ) (shPt A)
    let s' : SchemeHomOver (shPt A) F.gN := F.LN.mul (shPt A) s (F.LN.inv (shPt A) c)
    have hsc : F.LN.mul (shPt A) s' c = s := by
      show F.LN.mul (shPt A) (F.LN.mul (shPt A) s (F.LN.inv (shPt A) c)) c = s
      rw [F.LN.mul_assoc, F.LN.inv_mul_cancel, F.LN.mul_one]
    have hs' : F.specN s' = 0 := by
      have h := F.specN_mul s' c
      rw [hsc, hy] at h

      have : F.specN s' + φ = 0 + φ := by rw [zero_add]; exact h.symm
      exact add_right_cancel this
    obtain ⟨s₀, hs₀⟩ := (F.specN_eq_zero_iff s').mp hs'
    refine ⟨φ, ?_⟩

    have hfac : (shPt A) ≫ σ.1 = ((Λ.shLift s₀).1 ≫ F.openImm.1) ≫ COVERAsm.transl F (y φ) := by
      have e1 : (shPt A) ≫ σ.1 = s.1 := rfl
      have e2 : ((Λ.shLift s₀).1 ≫ F.openImm.1) = s'.1 := by rw [← hs₀]; rfl
      rw [e1, e2, COVERAsm.comp_transl, ← hsc]
    have hmem₀ : n₀ ∈ Set.range (F.openImm.1 ≫ COVERAsm.transl F (y φ)).base := by
      refine ⟨(Λ.shLift s₀).1.base (IsLocalRing.closedPoint ↥A), ?_⟩
      rw [← hσ, ← COVERAsm.shPt_base_closedPoint (A := A)]
      show ((Λ.shLift s₀).1 ≫ F.openImm.1 ≫ COVERAsm.transl F (y φ)).base (IsLocalRing.closedPoint ↥A) =
        (shPt A ≫ σ.1).base (IsLocalRing.closedPoint ↥A)
      rw [hfac, Category.assoc]
    haveI : IsOpenImmersion (F.openImm.1 ≫ COVERAsm.transl F (y φ)) := inferInstance
    change n ∈ Set.range (F.openImm.1 ≫ COVERAsm.transl F (y φ)).base
    exact hsp.mem_open (IsOpenImmersion.isOpen_range _) hmem₀
  ·
    obtain ⟨x, hx⟩ := NeronExtension.mem_range_openImm_of_base_ne_closedPoint N₀ p hpN₀ A hA Λ hΛ O F n hn
    refine ⟨0, x, ?_⟩
    have h0 : y 0 = F.LN.one (𝟙 _) := by simp only [y, if_true]
    show (F.openImm.1 ≫ COVERAsm.transl F (y 0)).base x = n
    rw [h0, COVERAsm.transl_one, Category.comp_id]
    exact hx

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul (solution)
