-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5497ea7f-9ed0-5c80-b24b-9e594c85973f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
import Theorems.Thm_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace Ws23RS3

theorem locIso_of_iso {S' : Type} [CommRing S'] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase p M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem locIso_congr {S' : Type} [CommRing S'] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S'))
    {M M' N N' : X.Modules} (eM : M ≅ N) (eM' : M' ≅ N') : LocIsoOnBase p M M' ↔ LocIsoOnBase p N N' := by
  have E := LocIsoOnBase.equivalence p
  constructor
  · intro h; exact E.trans (locIso_of_iso p eM.symm) (E.trans h (locIso_of_iso p eM'))
  · intro h; exact E.trans (locIso_of_iso p eM) (E.trans h (locIso_of_iso p eM'.symm))

theorem isInvertible_mumfordBundle {S' : Type} [CommRing S'] {A' : Scheme.{0}} (g : A' ⟶ Spec (CommRingCat.of S'))
    (L₀ : RelativeGroupLaw S' g) (𝓜 : A'.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    Scheme.Modules.IsInvertible (mumfordBundle g L₀ 𝓜) := by
  have hd := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓜).1
  unfold mumfordBundle
  exact (h𝓜.pullback _).tensor_monoidalV2 ((hd.pullback _).tensor_monoidalV2 (hd.pullback _))

end Ws23RS3

end

theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I) :
    ∃ J : I → Ideal S, ∀ (R : Type) [CommRing R] [Algebra S R],
      (∀ (L' : RelativeGroupLaw (R) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (R)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (R))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) ≫ act x) →
          (RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))).obj 𝓛)
            act' act'_over star ↔
            ∀ b : I, ∀ x ∈ J b, algebraMap S (R) x = 0)) := by
  classical

  let pX : pullback f f ⟶ Spec (CommRingCat.of S) := pullback.fst f f ≫ f
  have hX : AbelianSchemePropertyBundle S pX := GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing hA hA
  let Λ := mumfordBundle f L 𝓛
  have hΛ : Scheme.Modules.IsInvertible Λ := Ws23RS3.isInvertible_mumfordBundle f L 𝓛 h𝓛

  let sS : I → (pullback f f ⟶ pullback f f) := fun b =>
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let sS' : I → (pullback f f ⟶ pullback f f) := fun b =>
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)

  have key : ∀ b : I, ∃ Jb : Ideal S, ∀ (R : Type) [CommRing R] (φ : S →+* R) {A' : Scheme.{0}}
      {f' : A' ⟶ Spec (CommRingCat.of R)} (g : A' ⟶ pullback f f),
      IsPullback g f' pX (Spec.map (CommRingCat.ofHom φ)) →
        (LocIsoOnBase f' ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (sS b)).obj Λ))
            ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (sS' b)).obj Λ)) ↔ ∀ x ∈ Jb, φ x = 0) := by
    intro b
    obtain ⟨Z, ι, hι, -, hZ⟩ :=
      GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback
        (L.prod L) hX ((Scheme.Modules.pullback (sS b)).obj Λ) ((Scheme.Modules.pullback (sS' b)).obj Λ)
        (hΛ.pullback _) (hΛ.pullback _)
    haveI := hι
    obtain ⟨Jb, hJb⟩ :=
      AlgebraicGeometry.IsClosedImmersion.exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero ι
    refine ⟨Jb, fun R _ φ A' f' g hg => ?_⟩
    rw [← hZ R φ g hg, hJb R φ]
  choose J hJ using key
  refine ⟨J, fun R _ _ L' hL' act' act'_over hact' => ?_⟩

  let σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let g₀ : pullback f σ ⟶ A := pullback.fst f σ
  let fR : pullback f σ ⟶ Spec (CommRingCat.of R) := pullback.snd f σ
  have hg₀ : IsPullback g₀ fR f σ := IsPullback.of_hasPullback f σ
  let gg : pullback fR fR ⟶ pullback f f :=
    pullback.lift (pullback.fst fR fR ≫ g₀) (pullback.snd fR fR ≫ g₀)
      (by rw [Category.assoc, Category.assoc, hg₀.w, ← Category.assoc, pullback.condition, Category.assoc])
  have hsq : IsPullback gg (pullback.fst fR fR ≫ fR) pX σ :=
    AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr f σ

  obtain ⟨eΛ⟩ := AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
    S R (algebraMap S R) f L fR L' g₀ hg₀ (fun t' P Q => hL' _ t' P Q) 𝓛 h𝓛

  let sR : I → (pullback fR fR ⟶ pullback fR fR) := fun b =>
    pullback.lift (pullback.fst fR fR) (pullback.snd fR fR ≫ act' b) (by rw [Category.assoc, act'_over]; exact pullback.condition)
  let sR' : I → (pullback fR fR ⟶ pullback fR fR) := fun b =>
    pullback.lift (pullback.fst fR fR ≫ act' (star b)) (pullback.snd fR fR) (by rw [Category.assoc, act'_over]; exact pullback.condition)
  have hs : ∀ b, sR b ≫ gg = gg ≫ sS b := by
    intro b
    apply pullback.hom_ext
    · simp only [sR, sS, gg, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [sR, sS, gg, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact congrArg (fun k => pullback.snd fR fR ≫ k) (hact' b)
  have hs' : ∀ b, sR' b ≫ gg = gg ≫ sS' b := by
    intro b
    apply pullback.hom_ext
    · simp only [sR', sS', gg, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact congrArg (fun k => pullback.fst fR fR ≫ k) (hact' (star b))
    · simp only [sR', sS', gg, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

  have e₁ : ∀ b, (Scheme.Modules.pullback (sR b)).obj (mumfordBundle fR L' ((Scheme.Modules.pullback g₀).obj 𝓛)) ≅
      (Scheme.Modules.pullback gg).obj ((Scheme.Modules.pullback (sS b)).obj Λ) := fun b =>
    (Scheme.Modules.pullback (sR b)).mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp (sR b) gg).app Λ ≪≫
      (Scheme.Modules.pullbackCongr (hs b)).app Λ ≪≫ ((Scheme.Modules.pullbackComp gg (sS b)).app Λ).symm
  have e₂ : ∀ b, (Scheme.Modules.pullback (sR' b)).obj (mumfordBundle fR L' ((Scheme.Modules.pullback g₀).obj 𝓛)) ≅
      (Scheme.Modules.pullback gg).obj ((Scheme.Modules.pullback (sS' b)).obj Λ) := fun b =>
    (Scheme.Modules.pullback (sR' b)).mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp (sR' b) gg).app Λ ≪≫
      (Scheme.Modules.pullbackCongr (hs' b)).app Λ ≪≫ ((Scheme.Modules.pullbackComp gg (sS' b)).app Λ).symm

  have step : ∀ b, LocIsoOnBase (pullback.fst fR fR ≫ fR)
      ((Scheme.Modules.pullback (sR b)).obj (mumfordBundle fR L' ((Scheme.Modules.pullback g₀).obj 𝓛)))
      ((Scheme.Modules.pullback (sR' b)).obj (mumfordBundle fR L' ((Scheme.Modules.pullback g₀).obj 𝓛))) ↔
      ∀ x ∈ J b, algebraMap S R x = 0 := fun b =>
    (Ws23RS3.locIso_congr _ (e₁ b) (e₂ b)).trans (hJ b R (algebraMap S R) gg hsq)
  constructor
  · intro h b
    exact (step b).mp (h b)
  · intro h b
    exact (step b).mpr (h b)

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero (solution)
