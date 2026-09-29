-- Prove2me | solution 1 for GoodReductionJacobian.exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1cd30062-8922-5ef6-b965-711764aafc94

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mWs49InvAlg

theorem map_inv_of_map_mul {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
    (G₁ : RelativeGroupLaw R₁ f₁) (G₂ : RelativeGroupLaw R₂ f₂)
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R₂)}
    (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
    (hφ : ∀ x y, φ (G₁.mul t₁ x y) = G₂.mul t₂ (φ x) (φ y)) (x : SchemeHomOver t₁ f₁) :
    φ (G₁.inv t₁ x) = G₂.inv t₂ (φ x) := by
  letI := G₁.pointGroup t₁
  letI := G₂.pointGroup t₂
  exact map_inv (MonoidHom.mk' φ hφ) x

theorem inv_natural {R : Type u} [CommRing R] {A T T' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  map_inv_of_map_mul G G (GoodReductionJacobian.schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ) x

section

variable {R : Type u} [CommRing R] (I : Ideal R) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

abbrev bmap (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))

def upt (n : ℕ) : SchemeHomOver (adicThickeningToBase f I n) (adicThickeningToBase f I n) :=
  ⟨𝟙 _, Category.id_comp _⟩

def invMor (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ) :
    adicThickening f I n ⟶ adicThickening f I n :=
  ((L n).inv (adicThickeningToBase f I n) (upt I f n)).1

theorem invMor_toBase (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ) :
    invMor I f L n ≫ adicThickeningToBase f I n = adicThickeningToBase f I n :=
  ((L n).inv (adicThickeningToBase f I n) (upt I f n)).2

def push (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (P : SchemeHomOver t (adicThickeningToBase f I n)) :
    SchemeHomOver (t ≫ bmap I n) (adicThickeningToBase f I (n + 1)) :=
  ⟨P.1 ≫ adicThickeningTransition f I n, by
    rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩

@[scoped simp] theorem push_coe (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (P : SchemeHomOver t (adicThickeningToBase f I n)) : (push I f n P).1 = P.1 ≫ adicThickeningTransition f I n := rfl

theorem invMor_transition (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ bmap I n) (push I f n P) (push I f n Q)).1)
    (n : ℕ) :
    adicThickeningTransition f I n ≫ invMor I f L (n + 1) = invMor I f L n ≫ adicThickeningTransition f I n := by

  have hR : push I f n ((L n).inv _ (upt I f n)) = (L (n + 1)).inv _ (push I f n (upt I f n)) :=
    map_inv_of_map_mul (L n) (L (n + 1)) (push I f n) (fun P Q => Subtype.ext (hcompat n _ P Q)) (upt I f n)

  have hL : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
      (adicThickeningTransition_toBase f I n) ((L (n + 1)).inv _ (upt I f (n + 1))) =
      (L (n + 1)).inv _ (GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
        (adicThickeningTransition_toBase f I n) (upt I f (n + 1))) :=
    inv_natural (L (n + 1)) _ _ _ _ _
  have hpt : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
        (adicThickeningTransition_toBase f I n) (upt I f (n + 1)) = push I f n (upt I f n) := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, push_coe, upt, upt]
    simp only [Category.comp_id, Category.id_comp]
  rw [hpt] at hL
  have h1 := congrArg Subtype.val hL
  have h2 := congrArg Subtype.val hR
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [push_coe] at h2
  rw [invMor, invMor, h1, ← h2]

theorem comp_invMor (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (x : SchemeHomOver t (adicThickeningToBase f I n)) :
    x.1 ≫ invMor I f L n = ((L n).inv t x).1 := by
  have h := inv_natural (L n) (adicThickeningToBase f I n) t x.1 x.2 (upt I f n)
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (upt I f n) = x :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, upt]; exact Category.comp_id _)
  rw [hx] at h
  have h' := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h'
  exact h'

end

end P2mWs49InvAlg
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.P2mWs49InvAlg"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.P2mWs49InvAlg"

open P2mWs49InvAlg in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
          ⟨P.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) :
    ∃ i : A ⟶ A, i ≫ f = f ∧
      ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n := by
  obtain ⟨i, ⟨hi, hin⟩, -⟩ :=
    AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
      I f f N ι hι hιf N ι hι hιf (invMor I f L) (invMor_toBase I f L)
      (invMor_transition I f L (fun n _ t P Q => hcompat n t P Q))
  refine ⟨i, hi, ?_⟩
  intro n T t x
  rw [hin n, ← Category.assoc, comp_invMor]

end S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
end P2MW
export P2MW.S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete (solution)
