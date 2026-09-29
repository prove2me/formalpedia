-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_kernelTrivial_isLocalization_powers_of_kernelTrivial_isLocalization_primeCompl_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ea208a76-2d77-57ce-aeb0-27d772ca919a

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_kernelTrivial_isLocalization_powers_of_kernelTrivial_isLocalization_primeCompl_of_finite
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace KTSF22

open GoodReductionJacobian.RelativeGroupLaw

section Generic

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

abbrev bc (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

abbrev bcStr (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] :
    bc f X ⟶ Spec (CommRingCat.of X) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

abbrev bcFst (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : bc f X ⟶ A :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

def Compat {X : Type} [CommRing X] {AX : Scheme.{0}} (pX : AX ⟶ Spec (CommRingCat.of X))
    (jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)) (aX : AX ⟶ A) (haX : aX ≫ f = pX ≫ jX)
    (LX : RelativeGroupLaw X pX) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X)) (P Q : SchemeHomOver t' pX),
    (LX.mul t' P Q).1 ≫ aX =
      (L.mul (t' ≫ jX) ⟨P.1 ≫ aX, by rw [Category.assoc, haX, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ aX, by rw [Category.assoc, haX, ← Category.assoc, Q.2]⟩).1

theorem compat_baseChange {X : Type} [CommRing X] (jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)) :
    Compat L (pullback.snd f jX) jX (pullback.fst f jX) pullback.condition (L.baseChange jX) := by
  intro T t' P Q
  exact congrArg Subtype.val (baseChangePointToBase_mul jX L t' P Q)

theorem mul_coe_congr {R : Type} [CommRing R] {B : Scheme.{0}} {q : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R q)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ q) (P₂ Q₂ : SchemeHomOver t₂ q)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem compat_of_compat {X Y : Type} [CommRing X] [CommRing Y]
    {AX AY : Scheme.{0}} {pX : AX ⟶ Spec (CommRingCat.of X)} {pY : AY ⟶ Spec (CommRingCat.of Y)}
    {jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)} {jY : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of S)}
    {aX : AX ⟶ A} {aY : AY ⟶ A} (haX : aX ≫ f = pX ≫ jX) (hY : IsPullback aY pY f jY)
    (LX : RelativeGroupLaw X pX) (LY : RelativeGroupLaw Y pY)
    (hLX : Compat L pX jX aX haX LX) (hLY : Compat L pY jY aY hY.w LY)
    (ψ : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of Y)) (hψ : ψ ≫ jY = jX)
    (g : AX ⟶ AY) (hg₁ : g ≫ aY = aX) (hg₂ : g ≫ pY = pX ≫ ψ)
    (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X)) (P Q : SchemeHomOver t' pX) :
    (LX.mul t' P Q).1 ≫ g =
      (LY.mul (t' ≫ ψ) ⟨P.1 ≫ g, by rw [Category.assoc, hg₂, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg₂, ← Category.assoc, Q.2]⟩).1 := by
  apply hY.hom_ext
  · rw [Category.assoc, hg₁, hLX T t' P Q, hLY T (t' ≫ ψ)]
    exact mul_coe_congr L (by rw [Category.assoc, hψ]) _ _ _ _ (by simp only [Category.assoc, hg₁])
      (by simp only [Category.assoc, hg₁])
  · rw [(LY.mul (t' ≫ ψ) _ _).2, Category.assoc, hg₂, ← Category.assoc, (LX.mul t' P Q).2]

end Generic

section Struct

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem compat_comp {X Y : Type} [CommRing X] [CommRing Y]
    {AX : Scheme.{0}} {pX : AX ⟶ Spec (CommRingCat.of X)} {jX : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of S)}
    {aX : AX ⟶ A} (haX : aX ≫ f = pX ≫ jX) (LX : RelativeGroupLaw X pX) (hLX : Compat L pX jX aX haX LX)
    {AY : Scheme.{0}} {pY : AY ⟶ Spec (CommRingCat.of Y)} {jY : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of X)}
    {aY : AY ⟶ AX} (haY : aY ≫ pX = pY ≫ jY) (LY : RelativeGroupLaw Y pY) (hLY : Compat LX pY jY aY haY LY) :
    Compat L pY (jY ≫ jX) (aY ≫ aX) (by rw [Category.assoc, haX, ← Category.assoc, haY, Category.assoc]) LY := by
  intro T t' P Q
  rw [← Category.assoc, hLY T t' P Q, hLX T (t' ≫ jY)]
  exact mul_coe_congr L (Category.assoc _ _ _).symm _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)

theorem isPullback_of_proj {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] (ψ : X →+* Y)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S Y)))
    (φ : bc f Y ⟶ bc f X) (hφ₁ : φ ≫ bcFst f X = bcFst f Y) (hφ₂ : φ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom ψ)) :
    IsPullback φ (bcStr f Y) (bcStr f X) (Spec.map (CommRingCat.ofHom ψ)) := by
  refine IsPullback.of_right ?_ hφ₂ (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
  rw [hφ₁, hψ]
  exact IsPullback.of_hasPullback f _

theorem specMap_algebraMap_comp {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] [Algebra X Y]
    [IsScalarTower S X Y] :
    Spec.map (CommRingCat.ofHom (algebraMap X Y)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S Y)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem kernelTrivial_pullback_fst_of_lift {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra S X] [Algebra S Y] [Algebra X Y] [IsScalarTower S X Y] [Algebra X Z]
    (ψ : Y →+* Z) (hψ : ψ.comp (algebraMap X Y) = algebraMap X Z)
    (φ : bc f Y ⟶ bc f X) (hφ₁ : φ ≫ bcFst f X = bcFst f Y)
    (hφ₂ : φ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom (algebraMap X Y)))
    (LY : RelativeGroupLaw Y (bcStr f Y))
    (hLY : Compat L (bcStr f Y) (Spec.map (CommRingCat.ofHom (algebraMap S Y))) (bcFst f Y) pullback.condition LY)
    (𝓛' : (bc f X).Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hK : KernelTrivial (bcStr f Y) LY ((Scheme.Modules.pullback φ).obj 𝓛')) :
    KernelTrivial (pullback.snd (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Z))))
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S X)))).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap X Z))))
      ((Scheme.Modules.pullback (pullback.fst (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Z))))).obj 𝓛') := by

  have hφP : IsPullback φ (bcStr f Y) (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Y))) :=
    isPullback_of_proj (algebraMap X Y) specMap_algebraMap_comp φ hφ₁ hφ₂

  have hψS : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap X Y)) =
      Spec.map (CommRingCat.ofHom (algebraMap X Z)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]

  let gZ : pullback (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Z))) ⟶ bc f Y :=
    hφP.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [Category.assoc, hψS]; exact pullback.condition)
  have hgZ₁ : gZ ≫ φ = pullback.fst _ _ := hφP.lift_fst _ _ _
  have hgZ₂ : gZ ≫ bcStr f Y = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) := hφP.lift_snd _ _ _
  have hgZ : IsPullback gZ (pullback.snd (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Z)))) (bcStr f Y)
      (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ hgZ₂ hφP
    rw [hgZ₁, hψS]
    exact IsPullback.of_hasPullback _ _

  have hLZ : Compat L (pullback.snd (bcStr f X) (Spec.map (CommRingCat.ofHom (algebraMap X Z))))
      (Spec.map (CommRingCat.ofHom (algebraMap X Z)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
      (pullback.fst _ _ ≫ bcFst f X) _
      (((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S X)))).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap X Z))))) :=
    compat_comp L pullback.condition _ (compat_baseChange L _) pullback.condition _
      (compat_baseChange (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S X)))) _)
  have hmul := compat_of_compat L _ (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
    _ LY hLZ hLY (Spec.map (CommRingCat.ofHom ψ))
    (by rw [← specMap_algebraMap_comp (S := S) (X := X) (Y := Y), ← Category.assoc, hψS]) gZ
    (by rw [← hgZ₁, Category.assoc, hφ₁]) hgZ₂

  have hK' := AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback ψ hgZ LY _
    (fun {T} t' P Q => hmul T t' P Q) _ (h𝓛'.pullback φ) hK
  refine AlgebraicGeometry.Polarisation.kernelTrivial_of_iso Z _ _ _ _ ?_ hK'
  exact (Scheme.Modules.pullbackComp gZ φ).app 𝓛' ≪≫ (Scheme.Modules.pullbackCongr hgZ₁).app 𝓛'

end Struct

section Shrink

theorem exists_not_mem_forall_mem_of_finite {S : Type} [CommRing S] (𝔭 : PrimeSpectrum S) (r : S) (hr : r ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away r) C] [IsScalarTower S (Localization.Away r) C]
    [Module.Finite (Localization.Away r) C]
    (U : Set (PrimeSpectrum C)) (hU : IsOpen U)
    (hfib : ∀ Q : PrimeSpectrum C, Q.asIdeal.comap (algebraMap S C) = 𝔭.asIdeal → Q ∈ U) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ P : PrimeSpectrum C, algebraMap S C g ∉ P.asIdeal → P ∈ U := by
  classical

  let F : PrimeSpectrum C → PrimeSpectrum (Localization.Away r) := PrimeSpectrum.comap (algebraMap (Localization.Away r) C)
  let ι : PrimeSpectrum (Localization.Away r) → PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (Localization.Away r))
  have hFι : ∀ P : PrimeSpectrum C, ι (F P) = PrimeSpectrum.comap (algebraMap S C) P := fun P => by
    simp only [ι, F, ← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]

  have hFclosed : IsClosedMap F :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.isIntegral_def.1 inferInstance)
  have hι : Topology.IsOpenEmbedding ι := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away r) r

  have hdisj : Disjoint ((Submonoid.powers r : Submonoid S) : Set S) (𝔭.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hr (𝔭.isPrime.mem_of_pow_mem n hx)
  let 𝔭r : PrimeSpectrum (Localization.Away r) :=
    ⟨Ideal.map (algebraMap S (Localization.Away r)) 𝔭.asIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) _ _ 𝔭.isPrime hdisj⟩
  have h𝔭r : ι 𝔭r = 𝔭 :=
    PrimeSpectrum.ext (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers r) (Localization.Away r) 𝔭.isPrime hdisj)

  have hZ : IsClosed (F '' Uᶜ) := hFclosed _ hU.isClosed_compl
  have hV : IsOpen (ι '' (F '' Uᶜ)ᶜ) := hι.isOpenMap _ hZ.isOpen_compl
  have h𝔭V : 𝔭 ∈ ι '' (F '' Uᶜ)ᶜ := by
    refine ⟨𝔭r, ?_, h𝔭r⟩
    rintro ⟨Q, hQ, hQ'⟩
    apply hQ
    apply hfib
    have := congrArg PrimeSpectrum.asIdeal ((hFι Q).symm.trans ((congrArg ι hQ').trans h𝔭r))
    exact this
  obtain ⟨W, ⟨g, rfl⟩, hgW, hWV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭V hV
  refine ⟨g, hgW, fun P hP => ?_⟩
  have hPV : ι (F P) ∈ ι '' (F '' Uᶜ)ᶜ := by
    apply hWV
    rw [hFι]
    exact hP
  obtain ⟨y, hy, hyP⟩ := hPV
  have hyF : y = F P := hι.injective hyP
  subst hyF
  by_contra hPU
  exact hy ⟨P, hPU, rfl⟩

end Shrink

section Main

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem kernelTrivial_chart {C W Cg Z : Type} [CommRing C] [CommRing W] [CommRing Cg] [CommRing Z]
    [Algebra S C] [Algebra C W] [Algebra S Cg] [Algebra C Cg] [IsScalarTower S C Cg] [Algebra Cg Z]
    (ψ : W →+* Z) (hψ : ψ.comp (algebraMap C W) = (algebraMap Cg Z).comp (algebraMap C Cg))
    (φg : bc f Cg ⟶ bc f C) (hφg₁ : φg ≫ bcFst f C = bcFst f Cg)
    (hφg₂ : φg ≫ bcStr f C = bcStr f Cg ≫ Spec.map (CommRingCat.ofHom (algebraMap C Cg)))
    (Lg : RelativeGroupLaw Cg (bcStr f Cg))
    (hLg : Compat L (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap S Cg))) (bcFst f Cg) pullback.condition Lg)
    (𝓛' : (bc f C).Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hK : KernelTrivial (pullback.snd (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))))
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap C W))))
      ((Scheme.Modules.pullback (pullback.fst (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))))).obj 𝓛')) :
    KernelTrivial (pullback.snd (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))))
      (Lg.baseChange (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))))
      ((Scheme.Modules.pullback (pullback.fst (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))))).obj
        ((Scheme.Modules.pullback φg).obj 𝓛')) := by
  have hφgP : IsPullback φg (bcStr f Cg) (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C Cg))) :=
    isPullback_of_proj (algebraMap C Cg) specMap_algebraMap_comp φg hφg₁ hφg₂
  have hψS : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap C W)) =
      Spec.map (CommRingCat.ofHom (algebraMap Cg Z)) ≫ Spec.map (CommRingCat.ofHom (algebraMap C Cg)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]

  let gT : pullback (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))) ⟶
      pullback (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))) :=
    pullback.lift (pullback.fst _ _ ≫ φg) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [Category.assoc, hφg₂, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hψS])
  have hgT₁ : gT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φg := pullback.lift_fst _ _ _
  have hgT₂ : gT ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
  have hgT : IsPullback gT (pullback.snd (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))))
      (pullback.snd (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W)))) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ hgT₂
      (IsPullback.of_hasPullback (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))))
    rw [hgT₁, hψS]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) hφgP

  have hSrc : IsPullback (pullback.fst (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))) ≫ bcFst f C)
      (pullback.snd (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W)))) f
      (Spec.map (CommRingCat.ofHom (algebraMap C W)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C))) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)

  have hLT : Compat L (pullback.snd (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg Z))))
      (Spec.map (CommRingCat.ofHom (algebraMap Cg Z)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S Cg)))
      (pullback.fst _ _ ≫ bcFst f Cg) _ (Lg.baseChange (Spec.map (CommRingCat.ofHom (algebraMap Cg Z)))) :=
    compat_comp L pullback.condition Lg hLg pullback.condition _ (compat_baseChange Lg _)
  have hLS : Compat L (pullback.snd (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C W))))
      (Spec.map (CommRingCat.ofHom (algebraMap C W)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
      (pullback.fst _ _ ≫ bcFst f C) _
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap C W)))) :=
    compat_comp L pullback.condition _ (compat_baseChange L _) pullback.condition _
      (compat_baseChange (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))) _)
  have hmul := compat_of_compat L _ hSrc _ _ hLT hLS (Spec.map (CommRingCat.ofHom ψ))
    (by rw [← Category.assoc, hψS, Category.assoc, specMap_algebraMap_comp]) gT
    (by rw [← Category.assoc, hgT₁, Category.assoc, hφg₁]) hgT₂
  have hK' := AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback ψ hgT _ _
    (fun {T} t' P Q => hmul T t' P Q) _ (h𝓛'.pullback _) hK
  refine AlgebraicGeometry.Polarisation.kernelTrivial_of_iso Z _ _ _ _ ?_ hK'
  exact (Scheme.Modules.pullbackComp gT _).app 𝓛' ≪≫ (Scheme.Modules.pullbackCongr hgT₁).app 𝓛' ≪≫
    ((Scheme.Modules.pullbackComp (pullback.fst _ _) φg).app 𝓛').symm

end Main

end KTSF22

open KTSF22 GoodReductionJacobian.RelativeGroupLaw in

theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (𝔭 : PrimeSpectrum S)
    (r : S) (hr : r ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away r) C] [IsScalarTower S (Localization.Away r) C]
    (hC : Module.Finite (Localization.Away r) C)
    (𝓛' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (C𝔭 : Type) [CommRing C𝔭] [Algebra S C𝔭] [Algebra C C𝔭] [IsScalarTower S C C𝔭]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C𝔭]
    (φ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
    (hφ₁ : φ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))))
    (hφ₂ : φ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C C𝔭)))
    (L𝔭 : RelativeGroupLaw C𝔭 (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭)))))
    (hL𝔭 : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C𝔭))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))))),
        (L𝔭.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C𝔭)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (hK : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C𝔭)))) L𝔭
      ((Scheme.Modules.pullback φ).obj 𝓛')) :
    ∃ (g : S) (_ : g ∉ 𝔭.asIdeal),
      ∀ (Cg : Type) [CommRing Cg] [Algebra S Cg] [Algebra C Cg] [IsScalarTower S C Cg]
        [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers g)) Cg]
        (φg : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
        (_ : φg ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))))
        (_ : φg ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))) ≫ Spec.map (CommRingCat.ofHom (algebraMap C Cg)))
        (Lg : RelativeGroupLaw Cg (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Cg)))))
        (_ : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Cg))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))))),
            (Lg.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))) =
              (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Cg)))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Cg))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1),
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Cg)))) Lg
          ((Scheme.Modules.pullback φg).obj 𝓛') := by
  classical

  haveI : Module.Finite (Localization.Away r) C := hC
  haveI : IsNoetherianRing (Localization.Away r) := IsLocalization.isNoetherianRing (Submonoid.powers r) _ inferInstance
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing (Localization.Away r) C
  have hAC : AbelianSchemePropertyBundle C (bcStr f C) :=
    hA.of_isPullback (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S C))))

  have hunit : ∀ Q : {Q : PrimeSpectrum C // Q.asIdeal.comap (algebraMap S C) = 𝔭.asIdeal},
      ∀ y : Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl,
        IsUnit (algebraMap C (Localization.AtPrime Q.1.asIdeal) y) := by
    rintro ⟨Q, hQ⟩ ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.1 hy
    have hsQ : algebraMap S C s ∈ Q.asIdeal.primeCompl := by
      intro h
      apply hs
      show s ∈ 𝔭.asIdeal
      rw [← hQ]
      exact h
    exact IsLocalization.map_units (M := Q.asIdeal.primeCompl) (Localization.AtPrime Q.asIdeal) ⟨algebraMap S C s, hsQ⟩
  have step := fun Q : {Q : PrimeSpectrum C // Q.asIdeal.comap (algebraMap S C) = 𝔭.asIdeal} =>
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
      (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))) hAC 𝓛' h𝓛' Q.1
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))).baseChange _)
      (compat_baseChange (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))) _)
      (kernelTrivial_pullback_fst_of_lift L (IsLocalization.lift (hunit Q)) (IsLocalization.lift_comp _)
        φ hφ₁ hφ₂ L𝔭 hL𝔭 𝓛' h𝓛' hK)
  choose hfun hspec using step

  obtain ⟨g, hg𝔭, hgU⟩ := exists_not_mem_forall_mem_of_finite 𝔭 r hr C
    (⋃ Q, (PrimeSpectrum.basicOpen (hfun Q) : Set (PrimeSpectrum C)))
    (isOpen_iUnion fun Q => (PrimeSpectrum.basicOpen (hfun Q)).isOpen)
    (fun Q hQ => Set.mem_iUnion.2 ⟨⟨Q, hQ⟩, (hspec ⟨Q, hQ⟩).1⟩)
  refine ⟨g, hg𝔭, fun Cg _ _ _ _ _ φg hφg₁ hφg₂ Lg hLg => ?_⟩

  have hcovCg : ∀ x : PrimeSpectrum Cg,
      ∃ Q, x ∈ (PrimeSpectrum.basicOpen (algebraMap C Cg (hfun Q)) : Set (PrimeSpectrum Cg)) := by
    intro x
    have hx : algebraMap S C g ∉ (PrimeSpectrum.comap (algebraMap C Cg) x).asIdeal := by
      intro h
      have hu : IsUnit (algebraMap C Cg (algebraMap S C g)) :=
        IsLocalization.map_units Cg ⟨algebraMap S C g, Algebra.mem_algebraMapSubmonoid_of_mem ⟨g, Submonoid.mem_powers g⟩⟩
      exact x.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.1 (hgU _ hx)
    exact ⟨Q, hQ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun Q => (PrimeSpectrum.basicOpen (algebraMap C Cg (hfun Q)) : Set (PrimeSpectrum Cg)))
    (fun Q => (PrimeSpectrum.basicOpen _).isOpen) (fun x _ => Set.mem_iUnion.2 (hcovCg x))
  let ρ : Fin t.card → Cg := fun i => algebraMap C Cg (hfun (t.equivFin.symm i).1)
  have hρ : Ideal.span (Set.range ρ) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨Q, hQt, hxQ⟩ : ∃ Q ∈ t, x ∈ (PrimeSpectrum.basicOpen (algebraMap C Cg (hfun Q)) : Set _) := by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨Q, hQt⟩, ?_⟩
    show x ∈ (PrimeSpectrum.basicOpen (algebraMap C Cg (hfun (t.equivFin.symm (t.equivFin ⟨Q, hQt⟩)).1)) : Set _)
    rw [Equiv.symm_apply_apply]
    exact hxQ

  refine AlgebraicGeometry.Polarisation.KernelTrivial.of_forall_away_of_isInvertible (bcStr f Cg) Lg ρ hρ
    (fun i => pullback (bcStr f Cg) (Spec.map (CommRingCat.ofHom (algebraMap Cg (Localization.Away (ρ i))))))
    (fun i => pullback.snd _ _) (fun i => pullback.fst _ _) (fun i => IsPullback.of_hasPullback _ _)
    (fun i => Lg.baseChange _) (fun i {T} t' x y => compat_baseChange Lg _ T t' x y)
    ((Scheme.Modules.pullback φg).obj 𝓛') (h𝓛'.pullback φg) (fun i => ?_)
  have hu : IsUnit (((algebraMap Cg (Localization.Away (ρ i))).comp (algebraMap C Cg)) (hfun (t.equivFin.symm i).1)) :=
    IsLocalization.Away.algebraMap_isUnit (ρ i)
  exact kernelTrivial_chart L (IsLocalization.Away.lift (hfun (t.equivFin.symm i).1) hu)
    (IsLocalization.Away.lift_comp _ hu) φg hφg₁ hφg₂ Lg hLg 𝓛' h𝓛'
    ((hspec (t.equivFin.symm i)).2 _ (compat_baseChange (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C)))) _))

end

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_kernelTrivial_isLocalization_powers_of_kernelTrivial_isLocalization_primeCompl_of_finite
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_kernelTrivial_isLocalization_powers_of_kernelTrivial_isLocalization_primeCompl_of_finite (solution)
