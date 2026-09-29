-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/677fa141-62f6-5878-bdc2-7e345ac6c429

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
import Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.IsCommutative RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.IsCommutative.baseChange RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul baseChangePointToBase_coe baseChange baseChangePointToBase_mul IsCommutative.baseChange fibre exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
namespace FgAbelianDescent
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem baseChange_mul_fst {S S' : Type u} [CommRing S] [CommRing S']
    (u : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (pullback.snd f u)) :
    ((G.baseChange u).mul t' x y).1 ≫ pullback.fst f u =
      (G.mul (t' ≫ u)
        ⟨x.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul u G t' x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
  exact h

theorem mul_val_congr {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

section Transport

variable {S : Type u} [CommRing S] {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)}
  {fY : Y ⟶ Spec (CommRingCat.of S)} (e : X ≅ Y) (he : e.hom ≫ fY = fX)

include he in
theorem inv_comp_eq_of_hom_comp_eq : e.inv ≫ fX = fY := by
  rw [← he, Iso.inv_hom_id_assoc]

def pointBack {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fY) : SchemeHomOver t fX :=
  ⟨x.1 ≫ e.inv, by rw [Category.assoc, inv_comp_eq_of_hom_comp_eq e he, x.2]⟩

def pointForth {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fX) : SchemeHomOver t fY :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

@[scoped simp] theorem pointBack_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fY) :
    (pointBack e he x).1 = x.1 ≫ e.inv := rfl

@[scoped simp] theorem pointForth_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fX) :
    (pointForth e he x).1 = x.1 ≫ e.hom := rfl

@[scoped simp] theorem pointBack_pointForth {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fX) :
    pointBack e he (pointForth e he x) = x :=
  Subtype.ext (by simp)

@[scoped simp] theorem pointForth_pointBack {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t fY) :
    pointForth e he (pointBack e he x) = x :=
  Subtype.ext (by simp)

def transportIso (G : RelativeGroupLaw S fX) : RelativeGroupLaw S fY where
  mul t x y := pointForth e he (G.mul t (pointBack e he x) (pointBack e he y))
  one t := pointForth e he (G.one t)
  inv t x := pointForth e he (G.inv t (pointBack e he x))
  mul_assoc t x y z := by simp only [pointBack_pointForth, G.mul_assoc]
  one_mul t x := by simp only [pointBack_pointForth, G.one_mul, pointForth_pointBack]
  mul_one t x := by simp only [pointBack_pointForth, G.mul_one, pointForth_pointBack]
  inv_mul_cancel t x := by simp only [pointBack_pointForth, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    have hb : ∀ z : SchemeHomOver t fY, pointBack e he (schemeHomOverComp ψ hψ z) =
        schemeHomOverComp ψ hψ (pointBack e he z) := fun z => Subtype.ext (Category.assoc _ _ _)
    rw [hb, hb, ← G.mul_natural]
    simp only [schemeHomOverComp_coe, pointForth_coe, Category.assoc]

@[scoped simp] theorem transportIso_mul_coe (G : RelativeGroupLaw S fX) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x y : SchemeHomOver t fY) :
    ((transportIso e he G).mul t x y).1 = (G.mul t (pointBack e he x) (pointBack e he y)).1 ≫ e.hom := rfl

theorem transportIso_hom (G : RelativeGroupLaw S fX) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x y : SchemeHomOver t fX) :
    (G.mul t x y).1 ≫ e.hom =
      ((transportIso e he G).mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩
        ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1 := by
  rw [transportIso_mul_coe]
  congr 1
  apply mul_val_congr G rfl
  · simp
  · simp

theorem transportIso_isCommutative {G : RelativeGroupLaw S fX} (hG : G.IsCommutative) :
    (transportIso e he G).IsCommutative := fun t x y => by
  apply Subtype.ext
  rw [transportIso_mul_coe, transportIso_mul_coe, hG.mul_comm]

end Transport

theorem geometricallyConnected_of_bundle {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hX : AbelianSchemePropertyBundle R f) :
    GeometricallyConnected f := by
  haveI : Smooth f := hX.smooth
  haveI : IsProper f := hX.proper
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  let Y : Scheme.{u} := Spec (CommRingCat.of R)
  let k : Type u := ↥(Y.residueField s)
  let ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Y.fromSpecResidueField s
  let Lk : RelativeGroupLaw k (pullback.snd f ι) := L.baseChange ι
  haveI : ConnectedSpace ↥(pullback f ι) := by
    have h1 : _root_.IsConnected (f.base ⁻¹' {s}) := hX.connectedFibres s
    haveI h2 : ConnectedSpace ↥(f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp h1
    exact (Homeomorph.connectedSpace_iff (f.fiberHomeo s).symm).mp h2
  obtain ⟨G₀, i, L₀, hopen, hclosed, _, _, hgc, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k Lk
  rw [PreconnectedSpace.connectedComponent_eq_univ] at hrange
  haveI : Surjective i := ⟨Set.range_eq_univ.mp hrange⟩
  haveI := hgc
  exact AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective i (pullback.snd f ι)

theorem bundle_of_geometricallyConnected {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} [Smooth f] [IsProper f] [GeometricallyConnected f] (L : RelativeGroupLaw R f) :
    AbelianSchemePropertyBundle R f :=
  ⟨inferInstance, inferInstance, fun s => f.isConnected_preimage_singleton s, ⟨L⟩⟩

section Stages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

abbrev bT (T : Subalgebra A₀ A) : (Spec (CommRingCat.of ↥T) : Scheme.{u}) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))

abbrev uA (T : Subalgebra A₀ A) : (Spec (CommRingCat.of A) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥T A))

abbrev uT {T₁ T₂ : Subalgebra A₀ A} (h : T₁ ≤ T₂) :
    (Spec (CommRingCat.of ↥T₂) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T₁) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

theorem uA_uT {T₁ T₂ : Subalgebra A₀ A} (h : T₁ ≤ T₂) : uA T₂ ≫ uT h = uA T₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

variable (T : Subalgebra A₀ A) (T' : Subalgebra ↥T A)

def flat : Subalgebra A₀ A := T'.restrictScalars A₀

theorem le_flat : T ≤ flat T T' := fun x hx => T'.algebraMap_mem (⟨x, hx⟩ : ↥T)

theorem flat_fg (hT : T.FG) (hT' : T'.FG) : (flat T T').FG := by
  rw [Subalgebra.fg_iff_finiteType] at hT hT' ⊢
  haveI := hT
  haveI := hT'
  haveI : Algebra.FiniteType A₀ ↥T' := Algebra.FiniteType.trans (S := ↥T) inferInstance inferInstance
  exact this

def flatHom : ↥T' →+* ↥(flat T T') where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev uF : (Spec (CommRingCat.of ↥(flat T T')) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T') :=
  Spec.map (CommRingCat.ofHom (flatHom T T'))

theorem uF_comp : uF T T' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')) = uT (le_flat T T') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem uA_uF : uA (flat T T') ≫ uF T T' = Spec.map (CommRingCat.ofHom (algebraMap ↥T' A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

variable {T T'}

theorem isNoetherianRing_stage [IsNoetherianRing A₀] (hT : T.FG) : IsNoetherianRing ↥T := by
  haveI := (Subalgebra.fg_iff_finiteType T).mp hT
  exact Algebra.FiniteType.isNoetherianRing A₀ ↥T

theorem isPullback_lift_of_fac {X Y C B B' : Scheme.{u}} {π : X ⟶ Y} {f : X ⟶ C} {fY : Y ⟶ B} {b : C ⟶ B}
    (hπ : IsPullback π f fY b) (v : B' ⟶ B) (c : C ⟶ B') (hc : c ≫ v = b) :
    IsPullback (pullback.lift π (f ≫ c) (by rw [Category.assoc, hc, hπ.w])) f (pullback.snd fY v) c := by
  refine IsPullback.of_right (h₁₂ := pullback.fst fY v) (h₂₂ := v) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback fY v)
  rw [pullback.lift_fst, hc]
  exact hπ

theorem prop_snd_of_isPullback {X Y C B : Scheme.{u}} {π : X ⟶ Y} {f : X ⟶ C} {fY : Y ⟶ B} {b : C ⟶ B}
    (hπ : IsPullback π f fY b) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (h : P f) :
    P (pullback.snd fY b) := by
  rw [← hπ.isoPullback_hom_snd] at h
  exact (P.cancel_left_of_respectsIso _ _).mp h

theorem isPullback_paste {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S)
    (h : b ≫ a = c) :
    IsPullback (pullback.fst (pullback.snd f a) b ≫ pullback.fst f a) (pullback.snd (pullback.snd f a) b) f c := by
  rw [← h]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback f a)

def rebaseIso {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S) (h : b ≫ a = c) :
    pullback (pullback.snd f a) b ≅ pullback f c :=
  (isPullback_paste f a b c h).isoIsPullback _ _ (IsPullback.of_hasPullback f c)

@[scoped simp] theorem rebaseIso_hom_snd {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S)
    (h : b ≫ a = c) : (rebaseIso f a b c h).hom ≫ pullback.snd f c = pullback.snd _ _ :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

theorem prop_snd_of_fac {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S)
    (h : b ≫ a = c) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
    (hP : P (pullback.snd f a)) : P (pullback.snd f c) := by
  have h1 : P (pullback.snd (pullback.snd f a) b) := P.pullback_snd _ _ hP
  have h2 : pullback.snd f c = (rebaseIso f a b c h).inv ≫ pullback.snd (pullback.snd f a) b := by
    rw [Iso.eq_inv_comp, rebaseIso_hom_snd]
  rw [h2]
  exact (P.cancel_left_of_respectsIso _ _).mpr h1

theorem prop_snd_uT_of_prop_snd_algebraMap {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of ↥T))
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
    (hP : P (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))))) :
    P (pullback.snd fY (uT (le_flat T T'))) :=
  prop_snd_of_fac fY _ (uF T T') _ (uF_comp T T') P hP

end Stages

end GoodReductionJacobian.RelativeGroupLaw.FgAbelianDescent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian.RelativeGroupLaw.FgAbelianDescent"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing.GoodReductionJacobian.RelativeGroupLaw.FgAbelianDescent"

open GoodReductionJacobian.RelativeGroupLaw.FgAbelianDescent in
set_option maxHeartbeats 6400000 in
theorem solution
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} (L : RelativeGroupLaw A f)
    (hX : AbelianSchemePropertyBundle A f) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (L₀ : RelativeGroupLaw ↥T f₀) (π : X ⟶ X₀)
        (hπ : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))),
        AbelianSchemePropertyBundle ↥T f₀ ∧ GeometricallyConnected f₀ ∧ (L.IsCommutative → L₀.IsCommutative) ∧
        ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver t f),
          (L.mul t x y).1 ≫ π =
            (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))
              ⟨x.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, x.2]⟩
              ⟨y.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, y.2]⟩).1 := by
  classical

  haveI : Smooth f := hX.smooth
  haveI : IsProper f := hX.proper
  haveI hGC : GeometricallyConnected f := geometricallyConnected_of_bundle L hX

  obtain ⟨T₁, hT₁, hs₁, Y₁, f₁, π₁, hlfp₁, hqc₁, hqs₁, hπ₁⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A₀) (A := A) f s
  haveI := hlfp₁
  haveI := hqc₁
  haveI := hqs₁

  haveI : Smooth (pullback.snd f₁ (uA T₁)) := prop_snd_of_isPullback hπ₁ @Smooth inferInstance
  obtain ⟨U₂, hU₂, -, hS₂⟩ :=
    AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd (A₀ := ↥T₁) (A := A) f₁ ∅
  let T₂ : Subalgebra A₀ A := flat T₁ U₂
  have hT₂ : T₂.FG := flat_fg T₁ U₂ hT₁ hU₂
  have h₁₂ : T₁ ≤ T₂ := le_flat T₁ U₂
  let Y₂ : Scheme.{u} := pullback f₁ (uT h₁₂)
  let f₂ : Y₂ ⟶ Spec (CommRingCat.of ↥T₂) := pullback.snd f₁ (uT h₁₂)
  haveI hS₂' : Smooth f₂ := prop_snd_uT_of_prop_snd_algebraMap f₁ @Smooth hS₂
  let π₂ : X ⟶ Y₂ := pullback.lift π₁ (f ≫ uA T₂) (by rw [Category.assoc, uA_uT, hπ₁.w])
  have hπ₂ : IsPullback π₂ f f₂ (uA T₂) := isPullback_lift_of_fac hπ₁ (uT h₁₂) (uA T₂) (uA_uT h₁₂)

  haveI : IsSeparated (pullback.snd f₂ (uA T₂)) := prop_snd_of_isPullback hπ₂ @IsSeparated inferInstance
  obtain ⟨U₃, hU₃, -, hSep₃⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A₀ := ↥T₂) (A := A) f₂ ∅
  let T₃ : Subalgebra A₀ A := flat T₂ U₃
  have hT₃ : T₃.FG := flat_fg T₂ U₃ hT₂ hU₃
  have h₂₃ : T₂ ≤ T₃ := le_flat T₂ U₃
  let Y₃ : Scheme.{u} := pullback f₂ (uT h₂₃)
  let f₃ : Y₃ ⟶ Spec (CommRingCat.of ↥T₃) := pullback.snd f₂ (uT h₂₃)
  haveI hSep₃' : IsSeparated f₃ := prop_snd_uT_of_prop_snd_algebraMap f₂ @IsSeparated hSep₃
  let π₃ : X ⟶ Y₃ := pullback.lift π₂ (f ≫ uA T₃) (by rw [Category.assoc, uA_uT, hπ₂.w])
  have hπ₃ : IsPullback π₃ f f₃ (uA T₃) := isPullback_lift_of_fac hπ₂ (uT h₂₃) (uA T₃) (uA_uT h₂₃)

  haveI : IsNoetherianRing ↥T₃ := isNoetherianRing_stage hT₃
  haveI : IsProper (pullback.snd f₃ (uA T₃)) := prop_snd_of_isPullback hπ₃ @IsProper inferInstance
  obtain ⟨U₄, hU₄, -, hP₄⟩ :=
    AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A₀ := ↥T₃) (A := A) f₃ ∅
  let T₄ : Subalgebra A₀ A := flat T₃ U₄
  have hT₄ : T₄.FG := flat_fg T₃ U₄ hT₃ hU₄
  have h₃₄ : T₃ ≤ T₄ := le_flat T₃ U₄
  let Y₄ : Scheme.{u} := pullback f₃ (uT h₃₄)
  let f₄ : Y₄ ⟶ Spec (CommRingCat.of ↥T₄) := pullback.snd f₃ (uT h₃₄)
  haveI hP₄' : IsProper f₄ := prop_snd_uT_of_prop_snd_algebraMap f₃ @IsProper hP₄
  let π₄ : X ⟶ Y₄ := pullback.lift π₃ (f ≫ uA T₄) (by rw [Category.assoc, uA_uT, hπ₃.w])
  have hπ₄ : IsPullback π₄ f f₄ (uA T₄) := isPullback_lift_of_fac hπ₃ (uT h₃₄) (uA T₄) (uA_uT h₃₄)

  haveI : IsNoetherianRing ↥T₄ := isNoetherianRing_stage hT₄
  haveI : GeometricallyConnected (pullback.snd f₄ (uA T₄)) :=
    prop_snd_of_isPullback hπ₄ @GeometricallyConnected inferInstance
  obtain ⟨U₅, hU₅, -, hG₅⟩ :=
    AlgebraicGeometry.GeometricallyConnected.exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
      (A₀ := ↥T₄) (A := A) f₄ ∅
  let T₅ : Subalgebra A₀ A := flat T₄ U₅
  have hT₅ : T₅.FG := flat_fg T₄ U₅ hT₄ hU₅
  have h₄₅ : T₄ ≤ T₅ := le_flat T₄ U₅
  let Y₅ : Scheme.{u} := pullback f₄ (uT h₄₅)
  let f₅ : Y₅ ⟶ Spec (CommRingCat.of ↥T₅) := pullback.snd f₄ (uT h₄₅)
  haveI hG₅' : GeometricallyConnected f₅ := prop_snd_uT_of_prop_snd_algebraMap f₄ @GeometricallyConnected hG₅
  let π₅ : X ⟶ Y₅ := pullback.lift π₄ (f ≫ uA T₅) (by rw [Category.assoc, uA_uT, hπ₄.w])
  have hπ₅ : IsPullback π₅ f f₅ (uA T₅) := isPullback_lift_of_fac hπ₄ (uT h₄₅) (uA T₅) (uA_uT h₄₅)

  let e₅ : X ≅ pullback f₅ (uA T₅) := hπ₅.isoPullback
  have he₅ : e₅.hom ≫ pullback.snd f₅ (uA T₅) = f := hπ₅.isoPullback_hom_snd
  let L' : RelativeGroupLaw A (pullback.snd f₅ (uA T₅)) := transportIso e₅ he₅ L
  obtain ⟨U₆, hU₆, -, L₆, c, hciso, hc_snd, hc_fst, hcmul, hccomm⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      (A₀ := ↥T₅) (A := A) f₅ L' ∅
  haveI := hciso
  let T : Subalgebra A₀ A := flat T₅ U₆
  have hT : T.FG := flat_fg T₅ U₆ hT₅ hU₆
  have h₅T : T₅ ≤ T := le_flat T₅ U₆
  have hsT : (↑s : Set A) ⊆ T := hs₁.trans (h₁₂.trans (h₂₃.trans (h₃₄.trans (h₄₅.trans h₅T))))

  let b₆ : (Spec (CommRingCat.of ↥U₆) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T₅) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₅ ↥U₆))
  let g₆ : pullback f₅ b₆ ⟶ Spec (CommRingCat.of ↥U₆) := pullback.snd f₅ b₆
  let a₆ : (Spec (CommRingCat.of A) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥U₆) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥U₆ A))

  let X₀ : Scheme.{u} := pullback g₆ (uF T₅ U₆)
  let f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T) := pullback.snd g₆ (uF T₅ U₆)
  let L₀ : RelativeGroupLaw ↥T f₀ := L₆.baseChange (uF T₅ U₆)
  haveI : Smooth f₀ := inferInstance
  haveI : IsProper f₀ := inferInstance
  haveI : GeometricallyConnected f₀ := inferInstance
  have hA₀ : AbelianSchemePropertyBundle ↥T f₀ := bundle_of_geometricallyConnected L₀

  have hfac : uA T ≫ uF T₅ U₆ = a₆ := uA_uF T₅ U₆

  let κ : pullback g₆ a₆ ⟶ X₀ :=
    pullback.lift (pullback.fst g₆ a₆) (pullback.snd g₆ a₆ ≫ uA T) (by rw [Category.assoc, hfac, pullback.condition])
  have hκ_fst : κ ≫ pullback.fst g₆ (uF T₅ U₆) = pullback.fst g₆ a₆ := pullback.lift_fst _ _ _
  have hκ_snd : κ ≫ f₀ = pullback.snd g₆ a₆ ≫ uA T := pullback.lift_snd _ _ _
  have hκ : IsPullback κ (pullback.snd g₆ a₆) f₀ (uA T) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst g₆ (uF T₅ U₆)) (h₂₂ := uF T₅ U₆) ?_ hκ_snd
      (IsPullback.of_hasPullback _ _)
    rw [hκ_fst, hfac]
    exact IsPullback.of_hasPullback _ _

  let ψ : X ⟶ pullback g₆ a₆ := e₅.hom ≫ c
  have hψ : ψ ≫ pullback.snd g₆ a₆ = f := by
    show (e₅.hom ≫ c) ≫ _ = f
    rw [Category.assoc, hc_snd, he₅]
  haveI : IsIso ψ := IsIso.comp_isIso
  have hψκ : IsPullback (ψ ≫ κ) f f₀ (uA T) := by
    have hsq : IsPullback ψ f (pullback.snd g₆ a₆) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hψ]⟩
    have := hsq.paste_horiz hκ
    rwa [Category.id_comp] at this
  refine ⟨T, hT, hsT, X₀, f₀, L₀, ψ ≫ κ, hψκ, hA₀, inferInstance,
    fun hL => RelativeGroupLaw.IsCommutative.baseChange (uF T₅ U₆) (hccomm (transportIso_isCommutative e₅ he₅ hL)), ?_⟩
  intro T' t x y

  have ha := transportIso_hom e₅ he₅ L t x y
  have hb := hcmul t ⟨x.1 ≫ e₅.hom, by rw [Category.assoc, he₅, x.2]⟩ ⟨y.1 ≫ e₅.hom, by rw [Category.assoc, he₅, y.2]⟩
  have hab : (L.mul t x y).1 ≫ ψ =
      ((L₆.baseChange a₆).mul t
        ⟨(x.1 ≫ e₅.hom) ≫ c, by rw [Category.assoc, hc_snd, Category.assoc, he₅, x.2]⟩
        ⟨(y.1 ≫ e₅.hom) ≫ c, by rw [Category.assoc, hc_snd, Category.assoc, he₅, y.2]⟩).1 := by
    show (L.mul t x y).1 ≫ (e₅.hom ≫ c) = _
    rw [← Category.assoc, ha, hb]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hκ_fst, ← Category.assoc, hab, baseChange_mul_fst _ L₆ t,
      baseChange_mul_fst _ L₆ (t ≫ uA T)]
    refine mul_val_congr L₆ ?_ _ _ _ _ ?_ ?_
    · rw [Category.assoc, hfac]
    · show ((x.1 ≫ e₅.hom) ≫ c) ≫ pullback.fst g₆ a₆ = (x.1 ≫ (e₅.hom ≫ c) ≫ κ) ≫ pullback.fst g₆ (uF T₅ U₆)
      simp only [Category.assoc, hκ_fst]
    · show ((y.1 ≫ e₅.hom) ≫ c) ≫ pullback.fst g₆ a₆ = (y.1 ≫ (e₅.hom ≫ c) ≫ κ) ≫ pullback.fst g₆ (uF T₅ U₆)
      simp only [Category.assoc, hκ_fst]
  · have h1 : ((L.mul t x y).1 ≫ ψ ≫ κ) ≫ f₀ = t ≫ uA T := by
      rw [Category.assoc, Category.assoc, hκ_snd, ← Category.assoc, ← Category.assoc, Category.assoc _ ψ, hψ,
        (L.mul t x y).2]
    exact h1.trans ((L₀.mul (t ≫ uA T) _ _).2).symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing (solution)
