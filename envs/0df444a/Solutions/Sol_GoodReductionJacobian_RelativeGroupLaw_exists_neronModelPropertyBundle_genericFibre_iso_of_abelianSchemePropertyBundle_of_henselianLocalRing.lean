-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0e354ec8-efc5-5624-b8e4-db5c954e2e4b

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
import Theorems.Thm_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
import Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
import Theorems.Thm_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory NeronModelInfra.ComponentReading.isDomain NeronModelInfra.MinimalComponentData.finite NeronModelInfra.ComponentReading.isDiscreteValuationRing NeronModelInfra.ComponentReading.locallyOfFiniteType NeronModelInfra.ComponentReading.smooth NeronModelInfra.MinimalComponentData.nonempty NeronModelInfra.ComponentReading.isOpenImmersion PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AffineDilatation.coe_divElem PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj NeronModelInfra.MinimalComponentData.mk.injEq NeronModelInfra.ComponentReading.mk.injEq NeronModelInfra.ComponentReading.mk.sizeOf_spec NeronModelInfra.MinimalComponentData.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.DescentAction.toTriple_fst_assoc AlgebraicGeometry.DescentAction.invol_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst AlgebraicGeometry.DescentAction.flipMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst_assoc AlgebraicGeometry.DescentAction.unitMap_snd AlgebraicGeometry.DescentAction.eRel_snd AlgebraicGeometry.DescentAction.toTriple_fst AlgebraicGeometry.DescentAction.invol_invol AlgebraicGeometry.DescentAction.proj₁₃_snd AlgebraicGeometry.DescentAction.eRel_snd_assoc AlgebraicGeometry.DescentAction.invol_invol_assoc AlgebraicGeometry.DescentAction.invol_act AlgebraicGeometry.DescentAction.actMap_fst_assoc AlgebraicGeometry.DescentAction.flipMap_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst AlgebraicGeometry.DescentAction.invol_act_assoc AlgebraicGeometry.DescentAction.invol_fst_assoc AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc AlgebraicGeometry.DescentAction.mk.injEq AlgebraicGeometry.DescentAction.flipMap_fst AlgebraicGeometry.DescentAction.proj₁₃_fst AlgebraicGeometry.DescentAction.invol_fst AlgebraicGeometry.DescentAction.unitMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_fst AlgebraicGeometry.DescentAction.toTriple_snd_assoc AlgebraicGeometry.DescentAction.invol_snd AlgebraicGeometry.DescentAction.actMap_snd AlgebraicGeometry.DescentAction.flipMap_snd AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc AlgebraicGeometry.DescentAction.mk.sizeOf_spec AlgebraicGeometry.DescentAction.toTriple_snd"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace F1H9

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)}

noncomputable abbrev gfMap {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    pullback (u ≫ f) (specGenericFibreInclusion R K) ⟶ pullback f (specGenericFibreInclusion R K) :=
  pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
    (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_snd {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd (u ≫ f) (specGenericFibreInclusion R K) := by
  rw [pullback.lift_snd, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_fst {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst (u ≫ f) (specGenericFibreInclusion R K) ≫ u :=
  pullback.lift_fst _ _ _

theorem exists_smooth_modelFamily [Smooth gK]
    (M₀ : ModelFamily R K gK) (hfin : Finite M₀.ι)
    (hM₀ : ∀ i, IsSeparated (M₀.str i) ∧ LocallyOfFiniteType (M₀.str i) ∧ QuasiCompact (M₀.str i))
    (hpts : M₀.CatchesIndexOnePoints) :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by
  classical

  have hK : ∀ i, Smooth (pullback.snd (M₀.str i) (specGenericFibreInclusion R K)) := fun i => by
    rw [← (M₀.chart i).2]
    infer_instance
  have H : ∀ i, ∃ (X' : Scheme.{u}) (u : X' ⟶ M₀.X i),
      Smooth (u ≫ M₀.str i) ∧ QuasiCompact (u ≫ M₀.str i) ∧ IsSeparated u ∧
      IsIso (gfMap K (M₀.str i) u) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (M₀.str i),
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ M₀.str i),
            x'.1 ≫ u = x.1 := fun i => by
    haveI := (hM₀ i).2.1; haveI := (hM₀ i).2.2
    exact NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension K (M₀.str i) (hK i)
  choose X' u hsm hqc hsep hiso hlift using H
  let M : ModelFamily R K gK :=
    { ι := M₀.ι
      X := X'
      str := fun i => u i ≫ M₀.str i
      chart := fun i => NeronModelInfra.schemeHomOverComp ⟨gfMap K (M₀.str i) (u i), gfMap_snd K (M₀.str i) (u i)⟩ (M₀.chart i)
      isOpenImmersion_chart := fun i => by
        haveI := hiso i
        show IsOpenImmersion (gfMap K (M₀.str i) (u i) ≫ (M₀.chart i).1)
        infer_instance }
  refine ⟨M, hfin, fun i => ?_, ?_⟩
  · haveI := hsm i; haveI := hqc i; haveI := hsep i; haveI := (hM₀ i).1
    refine ⟨hsm i, ?_, ?_, hqc i⟩
    · show IsSeparated (u i ≫ M₀.str i); infer_instance
    · show LocallyOfFiniteType (u i ≫ M₀.str i); infer_instance
  · intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ hidx a
    obtain ⟨i, x, hx⟩ := hpts R' K' hidx a
    obtain ⟨x', hx'⟩ := hlift i R' hidx x
    refine ⟨i, x', ?_⟩
    rw [← hx]
    apply Subtype.ext
    show (pointGenericFibre (K := K) (K' := K') x').1 ≫ gfMap K (M₀.str i) (u i) ≫ (M₀.chart i).1 =
      (pointGenericFibre (K := K) (K' := K') x).1 ≫ (M₀.chart i).1
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, gfMap_fst, ← Category.assoc, pointGenericFibre_coe_comp_fst, Category.assoc, hx',
        pointGenericFibre_coe_comp_fst]
    · rw [Category.assoc, gfMap_snd, pointGenericFibre_coe_comp_snd, pointGenericFibre_coe_comp_snd]

theorem isCommutative_genericFibre
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g) (LAK : RelativeGroupLaw K gK)
    (hc : LAK.IsCommutative)
    (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hemul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
        LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) :
    (LB.genericFibre K).IsCommutative := by
  intro T t x y
  have h := hemul t x y
  rw [hc, ← hemul t y x] at h
  apply Subtype.ext
  rw [← cancel_mono e.1]
  exact congrArg (fun s => s.1) h

end F1H9

open F1H9 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (LAK : RelativeGroupLaw K gK)
    (hAK : AbelianSchemePropertyBundle K gK) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      NeronModelPropertyBundle R K g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LB.mul t x y = LB.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) := by
  haveI : IsProper gK := hAK.proper
  haveI : Smooth gK := hAK.smooth
  haveI : GeometricallyIntegral gK := hAK.geometricallyIntegral
  have hc : LAK.IsCommutative :=
    GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral LAK
  obtain ⟨M₀, hfin₀, hM₀, hpts₀⟩ :=
    NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper (R := R) K gK
  obtain ⟨M, hfin, hM, hpts⟩ := exists_smooth_modelFamily K M₀ hfin₀
    (fun i => ⟨(hM₀ i).2.1, (hM₀ i).2.2.2.1, (hM₀ i).2.2.2.2⟩) hpts₀
  obtain ⟨B, g, LB, e, hsm, hsep, hloft, hqc, he, hemul, htw⟩ :=
    NeronModelInfra.exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
      (R := R) K LAK hc M hfin hM hpts
  haveI := hsm; haveI := hsep; haveI := hloft; haveI := hqc; haveI := he
  refine ⟨B, g, LB, e, ?_, ?_, he, hemul⟩
  · exact NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension K LB htw
  · have hgen : (LB.genericFibre K).IsCommutative := isCommutative_genericFibre K LB LAK hc e hemul
    have hLB : LB.IsCommutative :=
      GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isCommutative_genericFibre K LB hgen
    intro T t x y
    exact hLB t x y

end S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing (solution)
