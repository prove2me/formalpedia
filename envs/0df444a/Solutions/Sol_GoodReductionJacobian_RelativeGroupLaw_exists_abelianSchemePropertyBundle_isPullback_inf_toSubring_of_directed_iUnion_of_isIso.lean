-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5dd354e4-cb3b-5a64-844e-0ac98b8686aa

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative one inv mul baseChangePointToBase_coe baseChange baseChangePointToBase_mul fibre exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation"
namespace LimAB
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

def IsHomOver {S : Type u} [CommRing S] {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)}
    {fY : Y ⟶ Spec (CommRingCat.of S)} (GX : RelativeGroupLaw S fX) (GY : RelativeGroupLaw S fY)
    (c : X ⟶ Y) (hc : c ≫ fY = fX) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t fX),
    (GX.mul t x y).1 ≫ c =
      (GY.mul t ⟨x.1 ≫ c, by rw [Category.assoc, hc, x.2]⟩ ⟨y.1 ≫ c, by rw [Category.assoc, hc, y.2]⟩).1

theorem IsHomOver.comp {S : Type u} [CommRing S] {X Y W : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)}
    {fY : Y ⟶ Spec (CommRingCat.of S)} {fW : W ⟶ Spec (CommRingCat.of S)}
    {GX : RelativeGroupLaw S fX} {GY : RelativeGroupLaw S fY} {GW : RelativeGroupLaw S fW}
    {c : X ⟶ Y} {hc : c ≫ fY = fX} {d : Y ⟶ W} {hd : d ≫ fW = fY}
    (h₁ : IsHomOver GX GY c hc) (h₂ : IsHomOver GY GW d hd) :
    IsHomOver GX GW (c ≫ d) (by rw [Category.assoc, hd, hc]) := by
  intro T t x y
  rw [← Category.assoc, h₁ t x y, h₂ t]
  apply mul_val_congr GW rfl
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _

theorem IsHomOver.inv {S : Type u} [CommRing S] {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)}
    {fY : Y ⟶ Spec (CommRingCat.of S)} {GX : RelativeGroupLaw S fX} {GY : RelativeGroupLaw S fY}
    (c : X ≅ Y) (hc : c.hom ≫ fY = fX) (h : IsHomOver GX GY c.hom hc) :
    IsHomOver GY GX c.inv (by rw [← hc, Iso.inv_hom_id_assoc]) := by
  intro T t x y
  have hx : (x.1 ≫ c.inv) ≫ c.hom = x.1 := by rw [Category.assoc, c.inv_hom_id, Category.comp_id]
  have hy : (y.1 ≫ c.inv) ≫ c.hom = y.1 := by rw [Category.assoc, c.inv_hom_id, Category.comp_id]
  have key := h t ⟨x.1 ≫ c.inv, by rw [Category.assoc, ← hc, Iso.inv_hom_id_assoc, x.2]⟩
    ⟨y.1 ≫ c.inv, by rw [Category.assoc, ← hc, Iso.inv_hom_id_assoc, y.2]⟩
  rw [← cancel_mono c.hom, Category.assoc, c.inv_hom_id, Category.comp_id, key]
  apply mul_val_congr GY rfl
  · exact hx.symm
  · exact hy.symm

theorem abelianSchemePropertyBundle_of_iso {S : Type u} [CommRing S] {X Q : Scheme.{u}}
    {fX : X ⟶ Spec (CommRingCat.of S)} {fQ : Q ⟶ Spec (CommRingCat.of S)}
    (e : X ⟶ Q) [IsIso e] (he : e ≫ fQ = fX) (LX : RelativeGroupLaw S fX)
    (hQ : AbelianSchemePropertyBundle S fQ) : AbelianSchemePropertyBundle S fX := by
  refine ⟨?_, ?_, ?_, ⟨LX⟩⟩
  · rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e fQ).mpr hQ.smooth
  · rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e fQ).mpr hQ.proper
  · intro s
    have hset : fX.base ⁻¹' {s} = e.homeomorph ⁻¹' (fQ.base ⁻¹' {s}) := by
      rw [← he, Scheme.Hom.comp_base, ← Set.preimage_comp]
      rfl
    rw [hset, Homeomorph.isConnected_preimage]
    exact hQ.connectedFibres s

theorem bundle_of_geometricallyConnected {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} [Smooth f] [IsProper f] [GeometricallyConnected f] (K : RelativeGroupLaw R f) :
    AbelianSchemePropertyBundle R f :=
  ⟨inferInstance, inferInstance, fun s => f.isConnected_preimage_singleton s, ⟨K⟩⟩

section Towers

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

theorem toSubring_mono {E₁ E₂ : IntermediateField k Ω} (h : E₁ ≤ E₂) : E₁.toSubring ≤ E₂.toSubring :=
  fun _ hx => h hx

abbrev levMap (V : Subring Ω) {E₁ E₂ : IntermediateField k Ω} (h : E₁ ≤ E₂) :
    ↥(V ⊓ E₁.toSubring) →+* ↥(V ⊓ E₂.toSubring) :=
  Subring.inclusion (inf_le_inf_left V (toSubring_mono h))

abbrev fldMap {E₁ E₂ : IntermediateField k Ω} (h : E₁ ≤ E₂) : ↥E₁ →+* ↥E₂ :=
  (IntermediateField.inclusion h).toRingHom

@[scoped simp] theorem levMap_apply_coe (V : Subring Ω) {E₁ E₂ : IntermediateField k Ω} (h : E₁ ≤ E₂)
    (x : ↥(V ⊓ E₁.toSubring)) : ((levMap V h x : ↥(V ⊓ E₂.toSubring)) : Ω) = (x : Ω) := rfl

@[scoped simp] theorem fldMap_apply_coe {E₁ E₂ : IntermediateField k Ω} (h : E₁ ≤ E₂) (x : ↥E₁) :
    ((fldMap h x : ↥E₂) : Ω) = (x : Ω) := rfl

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] (F : ι → IntermediateField k Ω) (hF : Monotone F)

include hF in

theorem exists_le_forall_mem (t : Finset Ω) (ht : ∀ x ∈ t, ∃ i, x ∈ F i) (i₀ : ι) :
    ∃ i, i₀ ≤ i ∧ ∀ x ∈ t, x ∈ F i := by
  classical
  choose! g hg using ht
  obtain ⟨i, hi⟩ := Finset.exists_le (insert i₀ (t.image g))
  refine ⟨i, hi i₀ (Finset.mem_insert_self _ _), fun x hx => ?_⟩
  exact hF (hi (g x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hx))) (hg x hx)

def intAlgebra (S : Type u) [CommRing S] : Algebra (ULift.{u} ℤ) S :=
  ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom).toAlgebra

def intSubalgebra {S : Type u} [CommRing S] (B : Subring S) :
    letI := intAlgebra S
    Subalgebra (ULift.{u} ℤ) S :=
  letI := intAlgebra S
  { B with
    algebraMap_mem' := fun r => by
      show ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom) r ∈ B
      exact intCast_mem B _ }

theorem mem_intSubalgebra {S : Type u} [CommRing S] (B : Subring S) (x : S) :
    letI := intAlgebra S
    x ∈ intSubalgebra B ↔ x ∈ B :=
  Iff.rfl

variable (V : Subring Ω) (Z : IntermediateField k Ω)

def levelSubring (E : IntermediateField k Ω) : Subring ↥(V ⊓ Z.toSubring) :=
  (E.toSubring).comap (V ⊓ Z.toSubring).subtype

theorem mem_levelSubring (E : IntermediateField k Ω) (x : ↥(V ⊓ Z.toSubring)) : x ∈ levelSubring V Z E ↔ (x : Ω) ∈ E :=
  Iff.rfl

def stageToLevel (E : IntermediateField k Ω) {S' : Type u} [SetLike S' ↥(V ⊓ Z.toSubring)]
    [SubringClass S' ↥(V ⊓ Z.toSubring)] (T : S') (hT : ∀ x ∈ T, ((x : ↥(V ⊓ Z.toSubring)) : Ω) ∈ E) :
    ↥T →+* ↥(V ⊓ E.toSubring) where
  toFun x := ⟨((x : ↥(V ⊓ Z.toSubring)) : Ω), (x : ↥(V ⊓ Z.toSubring)).2.1, hT x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def fieldSubalgebra {Fj E : IntermediateField k Ω} (hjE : Fj ≤ E) (hEZ : E ≤ Z) :
    letI := (fldMap (hjE.trans hEZ)).toAlgebra
    Subalgebra ↥Fj ↥Z :=
  letI := (fldMap (hjE.trans hEZ)).toAlgebra
  { carrier := {z | (z : Ω) ∈ E}
    mul_mem' := fun ha hb => E.mul_mem ha hb
    one_mem' := E.one_mem
    add_mem' := fun ha hb => E.add_mem ha hb
    zero_mem' := E.zero_mem
    algebraMap_mem' := fun r => hjE r.2 }

def stageToField (E : IntermediateField k Ω) {S' : Type u} [SetLike S' ↥Z] [SubringClass S' ↥Z] (T : S')
    (hT : ∀ x ∈ T, ((x : ↥Z) : Ω) ∈ E) : ↥T →+* ↥E where
  toFun x := ⟨((x : ↥Z) : Ω), hT x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end Towers

end GoodReductionJacobian.RelativeGroupLaw.LimAB
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian.RelativeGroupLaw.LimAB"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian"

open GoodReductionJacobian.RelativeGroupLaw.LimAB in
set_option maxHeartbeats 6400000 in
theorem solution
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (V : Subring Ω)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (F : ι → IntermediateField k Ω) (hF : Monotone F)
    (Z : IntermediateField k Ω) (hFZ : ∀ i, F i ≤ Z) (hZ : ∀ x ∈ Z, ∃ i, x ∈ F i)
    (ρ : ↥(V ⊓ Z.toSubring) →+* ↥Z)
    (hρ : ∀ x : ↥(V ⊓ Z.toSubring), ((ρ x : ↥Z) : Ω) = (x : Ω))
    (τ : ∀ i, ↥(V ⊓ (F i).toSubring) →+* ↥(F i))
    (hτ : ∀ (i) (x : ↥(V ⊓ (F i).toSubring)), ((τ i x : ↥(F i)) : Ω) = (x : Ω))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of ↥(V ⊓ Z.toSubring))}
    (L : RelativeGroupLaw ↥(V ⊓ Z.toSubring) f) (hL : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle ↥(V ⊓ Z.toSubring) f)
    (i₀ : ι) {P₀ : Scheme.{u}} {f₀ : P₀ ⟶ Spec (CommRingCat.of ↥(F i₀))}
    [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀]
    (L₀ : RelativeGroupLaw ↥(F i₀) f₀)
    (e : pullback f (Spec.map (CommRingCat.ofHom ρ)) ⟶
      pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom)))
    [IsIso e]
    (he : e ≫ pullback.snd f₀ _ = pullback.snd f _)
    (hemul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥Z))
        (x y : SchemeHomOver t (pullback.snd f (Spec.map (CommRingCat.ofHom ρ)))),
      ((L.baseChange (Spec.map (CommRingCat.ofHom ρ))).mul t x y).1 ≫ e =
        ((L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom))).mul t
          ⟨x.1 ≫ e, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e, by rw [Category.assoc, he, y.2]⟩).1) :
    ∃ (i : ι) (hi : i₀ ≤ i) (Aᵢ : Scheme.{u}) (fᵢ : Aᵢ ⟶ Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)))
      (Lᵢ : RelativeGroupLaw ↥(V ⊓ (F i).toSubring) fᵢ) (_ : Lᵢ.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥(V ⊓ (F i).toSubring) fᵢ)
      (g : pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)) ⟶ Aᵢ)
      (hg : IsPullback g
        (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)))
        fᵢ (Spec.map (CommRingCat.ofHom (τ i)))),
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥(F i)))
        (x y : SchemeHomOver t
          (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)))),
        ((L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom))).mul
            t x y).1 ≫ g =
          (Lᵢ.mul (t ≫ Spec.map (CommRingCat.ofHom (τ i)))
            ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1 := by
  classical

  letI := intAlgebra ↥(V ⊓ Z.toSubring)
  haveI : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, -, Xc, fc, Lc, π, hπ, hAc, hgc, hcomm, hπmul⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := ULift.{u} ℤ) (A := ↥(V ⊓ Z.toSubring)) L hA ∅
  haveI := hgc
  haveI : Smooth fc := hAc.smooth
  haveI : IsProper fc := hAc.proper
  have hLc : Lc.IsCommutative := hcomm hL

  obtain ⟨t, ht⟩ := hT
  obtain ⟨j, hi₀j, hj⟩ := exists_le_forall_mem F hF (t.image fun x : ↥(V ⊓ Z.toSubring) => (x : Ω))
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact hZ _ y.2.2) i₀
  have hTj : ∀ x ∈ T, ((x : ↥(V ⊓ Z.toSubring)) : Ω) ∈ F j := by
    have hle : T ≤ intSubalgebra (levelSubring V Z (F j)) := by
      rw [← ht]
      exact Algebra.adjoin_le fun x hx => hj _ (Finset.mem_image_of_mem _ hx)
    exact fun x hx => hle hx
  let ψ : ↥T →+* ↥(V ⊓ (F j).toSubring) := stageToLevel V Z (F j) T hTj

  set gT : ∀ i, (Spec (CommRingCat.of ↥(V ⊓ Z.toSubring)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)) :=
    fun i => Spec.map (CommRingCat.ofHom (levMap V (hFZ i))) with hgT
  have hgTφ : ∀ (i i' : ι) (h : i ≤ i'), gT i' ≫ Spec.map (CommRingCat.ofHom (levMap V (hF h))) = gT i := by
    intro i i' h
    rw [hgT, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  let bT : (Spec (CommRingCat.of ↥(V ⊓ Z.toSubring)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥(V ⊓ Z.toSubring)))
  let vψ : (Spec (CommRingCat.of ↥(V ⊓ (F j).toSubring)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T) :=
    Spec.map (CommRingCat.ofHom ψ)
  have hgTψ : gT j ≫ vψ = bT := by
    rw [hgT, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

  let Aⱼ : Scheme.{u} := pullback fc vψ
  let fⱼ : Aⱼ ⟶ Spec (CommRingCat.of ↥(V ⊓ (F j).toSubring)) := pullback.snd _ _
  let Lⱼ : RelativeGroupLaw ↥(V ⊓ (F j).toSubring) fⱼ := Lc.baseChange _
  have hLⱼ : Lⱼ.IsCommutative := hLc.baseChange _
  have hAⱼ : AbelianSchemePropertyBundle ↥(V ⊓ (F j).toSubring) fⱼ := bundle_of_geometricallyConnected Lⱼ

  have hAⱼ' : ∀ (j' : ι) (h : j ≤ j'),
      AbelianSchemePropertyBundle ↥(V ⊓ (F j').toSubring)
        (pullback.snd fⱼ (Spec.map (CommRingCat.ofHom (levMap V (hF h))))) :=
    fun j' h => bundle_of_geometricallyConnected (Lⱼ.baseChange _)

  have hp₀w : π ≫ fc = (f ≫ gT j) ≫ vψ := by
    rw [Category.assoc, hgTψ]; exact hπ.w
  let p : A ⟶ Aⱼ := pullback.lift π (f ≫ gT j) hp₀w
  have hp_fst : p ≫ pullback.fst _ _ = π := pullback.lift_fst _ _ _
  have hp_snd : p ≫ fⱼ = f ≫ gT j := pullback.lift_snd _ _ _
  have hp : IsPullback p f fⱼ (gT j) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst fc vψ) (h₂₂ := vψ) ?_ hp_snd (IsPullback.of_hasPullback _ _)
    rw [hp_fst, hgTψ]
    exact hπ
  have hpmul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of ↥(V ⊓ Z.toSubring))) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ p =
        (Lⱼ.mul (t ≫ gT j) ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1 := by
    intro T' t x y
    apply pullback.hom_ext
    · rw [Category.assoc, hp_fst, hπmul t x y]
      refine Eq.trans ?_ (baseChange_mul_fst _ Lc (t ≫ gT j) _ _).symm
      apply mul_val_congr Lc
      · rw [Category.assoc, hgTψ]
      · show x.1 ≫ π = (x.1 ≫ p) ≫ pullback.fst _ _
        rw [Category.assoc, hp_fst]
      · show y.1 ≫ π = (y.1 ≫ p) ≫ pullback.fst _ _
        rw [Category.assoc, hp_fst]
    · have h1 : ((L.mul t x y).1 ≫ p) ≫ fⱼ = t ≫ gT j := by
        rw [Category.assoc, hp_snd, ← Category.assoc, (L.mul t x y).2]
      calc (L.mul t x y).1 ≫ p ≫ fⱼ = ((L.mul t x y).1 ≫ p) ≫ fⱼ := (Category.assoc _ _ _).symm
        _ = t ≫ gT j := h1
        _ = _ := ((Lⱼ.mul (t ≫ gT j) _ _).2).symm

  haveI : Smooth fⱼ := hAⱼ.smooth
  haveI : IsProper fⱼ := hAⱼ.proper

  let uj : (Spec (CommRingCat.of ↥(F j)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(V ⊓ (F j).toSubring)) :=
    Spec.map (CommRingCat.ofHom (τ j))
  let fX' : pullback fⱼ uj ⟶ Spec (CommRingCat.of ↥(F j)) := pullback.snd fⱼ uj
  let LX' : RelativeGroupLaw ↥(F j) fX' := Lⱼ.baseChange uj
  let ι₀j : (Spec (CommRingCat.of ↥(F j)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(F i₀)) :=
    Spec.map (CommRingCat.ofHom (fldMap (hF hi₀j)))
  let fY' : pullback f₀ ι₀j ⟶ Spec (CommRingCat.of ↥(F j)) := pullback.snd f₀ ι₀j
  let LY' : RelativeGroupLaw ↥(F j) fY' := L₀.baseChange ι₀j

  let gZ : ∀ i, (Spec (CommRingCat.of ↥Z) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(F i)) :=
    fun i => Spec.map (CommRingCat.ofHom (fldMap (hFZ i)))
  have hgZφ : ∀ (i i' : ι) (h : i ≤ i'), gZ i' ≫ Spec.map (CommRingCat.ofHom (fldMap (hF h))) = gZ i := by
    intro i i' h
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hρτ : Spec.map (CommRingCat.ofHom ρ) ≫ gT j = gZ j ≫ uj := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => Subtype.ext ?_
    show ((ρ (levMap V (hFZ j) x) : ↥Z) : Ω) = ((τ j x : ↥(F j)) : Ω)
    rw [hρ, hτ]
    rfl
  have hι₀ : gZ j ≫ ι₀j = Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have sqA : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom ρ)) ≫ p) (pullback.snd f (Spec.map (CommRingCat.ofHom ρ)))
      fⱼ (gZ j ≫ uj) := by
    rw [← hρτ]
    exact (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom ρ))).paste_horiz hp
  have sqX : IsPullback (pullback.fst fX' (gZ j) ≫ pullback.fst fⱼ uj) (pullback.snd fX' (gZ j)) fⱼ (gZ j ≫ uj) :=
    (IsPullback.of_hasPullback fX' (gZ j)).paste_horiz (IsPullback.of_hasPullback fⱼ uj)
  let cX : pullback f (Spec.map (CommRingCat.ofHom ρ)) ≅ pullback fX' (gZ j) := sqA.isoIsPullback _ _ sqX
  have hcX_fst : cX.hom ≫ pullback.fst fX' (gZ j) ≫ pullback.fst fⱼ uj = pullback.fst f _ ≫ p :=
    sqA.isoIsPullback_hom_fst _ _ sqX
  have hcX_snd : cX.hom ≫ pullback.snd fX' (gZ j) = pullback.snd f _ := sqA.isoIsPullback_hom_snd _ _ sqX

  have sqP := IsPullback.of_hasPullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom))
  have sqY : IsPullback (pullback.fst fY' (gZ j) ≫ pullback.fst f₀ ι₀j) (pullback.snd fY' (gZ j)) f₀
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom)) := by
    rw [← hι₀]
    exact (IsPullback.of_hasPullback fY' (gZ j)).paste_horiz (IsPullback.of_hasPullback f₀ ι₀j)
  let cY : pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom)) ≅
      pullback fY' (gZ j) := sqP.isoIsPullback _ _ sqY
  have hcY_fst : cY.hom ≫ pullback.fst fY' (gZ j) ≫ pullback.fst f₀ ι₀j = pullback.fst f₀ _ :=
    sqP.isoIsPullback_hom_fst _ _ sqY
  have hcY_snd : cY.hom ≫ pullback.snd fY' (gZ j) = pullback.snd f₀ _ := sqP.isoIsPullback_hom_snd _ _ sqY

  have hcXmul : IsHomOver (L.baseChange (Spec.map (CommRingCat.ofHom ρ))) (LX'.baseChange (gZ j)) cX.hom hcX_snd := by
    intro T t x y

    have keyR : ∀ z : SchemeHomOver t (pullback.snd fX' (gZ j)),
        (z.1 ≫ pullback.fst fX' (gZ j)) ≫ pullback.snd fⱼ uj = t ≫ gZ j := fun z => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]
    have keyL : ∀ w : SchemeHomOver t (pullback.snd f (Spec.map (CommRingCat.ofHom ρ))),
        ((w.1 ≫ cX.hom) ≫ pullback.fst fX' (gZ j)) ≫ pullback.snd fⱼ uj = t ≫ gZ j := fun w => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, Category.assoc w.1, hcX_snd, w.2]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hcX_fst, ← Category.assoc, baseChange_mul_fst _ L t x y, hpmul]
        conv_rhs => rw [Category.assoc, ← Category.assoc _ (pullback.fst fX' (gZ j)) (pullback.fst fⱼ uj),
          baseChange_mul_fst _ LX' t, baseChange_mul_fst _ Lⱼ]
        refine mul_val_congr Lⱼ ?_ _ _ _ _ ?_ ?_
        · rw [Category.assoc, Category.assoc, hρτ]
        · show (x.1 ≫ pullback.fst f _) ≫ p = ((x.1 ≫ cX.hom) ≫ pullback.fst fX' (gZ j)) ≫ pullback.fst fⱼ uj
          rw [Category.assoc, Category.assoc, Category.assoc, hcX_fst]
        · show (y.1 ≫ pullback.fst f _) ≫ p = ((y.1 ≫ cX.hom) ≫ pullback.fst fX' (gZ j)) ≫ pullback.fst fⱼ uj
          rw [Category.assoc, Category.assoc, Category.assoc, hcX_fst]
      · exact (keyL _).trans (keyR _).symm
    · rw [Category.assoc, hcX_snd, ((L.baseChange _).mul t x y).2]
      exact (((LX'.baseChange (gZ j)).mul t _ _).2).symm

  have hcYmul : IsHomOver (L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom)))
      (LY'.baseChange (gZ j)) cY.hom hcY_snd := by
    intro T t x y
    have keyR : ∀ z : SchemeHomOver t (pullback.snd fY' (gZ j)),
        (z.1 ≫ pullback.fst fY' (gZ j)) ≫ pullback.snd f₀ ι₀j = t ≫ gZ j := fun z => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]
    have keyL : ∀ w : SchemeHomOver t
        (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom))),
        ((w.1 ≫ cY.hom) ≫ pullback.fst fY' (gZ j)) ≫ pullback.snd f₀ ι₀j = t ≫ gZ j := fun w => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, Category.assoc w.1, hcY_snd, w.2]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hcY_fst, baseChange_mul_fst _ L₀ t x y]
        conv_rhs => rw [Category.assoc, ← Category.assoc _ (pullback.fst fY' (gZ j)) (pullback.fst f₀ ι₀j),
          baseChange_mul_fst _ LY' t, baseChange_mul_fst _ L₀]
        refine mul_val_congr L₀ ?_ _ _ _ _ ?_ ?_
        · rw [Category.assoc, hι₀]
        · show x.1 ≫ pullback.fst f₀ _ = ((x.1 ≫ cY.hom) ≫ pullback.fst fY' (gZ j)) ≫ pullback.fst f₀ ι₀j
          rw [Category.assoc, Category.assoc, hcY_fst]
        · show y.1 ≫ pullback.fst f₀ _ = ((y.1 ≫ cY.hom) ≫ pullback.fst fY' (gZ j)) ≫ pullback.fst f₀ ι₀j
          rw [Category.assoc, Category.assoc, hcY_fst]
      · exact (keyL _).trans (keyR _).symm
    · rw [Category.assoc, hcY_snd, ((L₀.baseChange _).mul t x y).2]
      exact (((LY'.baseChange (gZ j)).mul t _ _).2).symm

  have hemul' : IsHomOver (L.baseChange (Spec.map (CommRingCat.ofHom ρ)))
      (L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom))) e he :=
    fun _ t x y => hemul t x y
  let E : pullback fX' (gZ j) ⟶ pullback fY' (gZ j) := (cX.inv ≫ e) ≫ cY.hom
  haveI : IsIso E := inferInstance
  have hEmul := IsHomOver.comp (IsHomOver.comp (IsHomOver.inv cX hcX_snd hcXmul) hemul') hcYmul
  have hE : E ≫ pullback.snd fY' (gZ j) = pullback.snd fX' (gZ j) := by
    show ((cX.inv ≫ e) ≫ cY.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, hcY_snd, he, ← hcX_snd, Iso.inv_hom_id_assoc]

  letI algZ : Algebra ↥(F j) ↥Z := (fldMap (hFZ j)).toAlgebra
  obtain ⟨T', hT', -, hall⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥(F j)) (A := ↥Z) fX' fY' LX' LY' (asIso E) hE (fun t x y => hEmul t x y) ∅
  obtain ⟨t', ht'⟩ := hT'
  obtain ⟨i, hji, hi'⟩ := exists_le_forall_mem F hF (t'.image fun z : ↥Z => (z : Ω))
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact hZ _ y.2) j
  have hT'i : ∀ x ∈ T', ((x : ↥Z) : Ω) ∈ F i := by
    have hle : T' ≤ fieldSubalgebra Z (hF hji) (hFZ i) := by
      rw [← ht']
      exact Algebra.adjoin_le fun x hx => hi' _ (Finset.mem_image_of_mem _ hx)
    exact fun x hx => hle hx
  obtain ⟨eᵢ, heᵢ, heᵢmul⟩ := hall ↥(F i) (stageToField Z (F i) T' hT'i) (fldMap (hF hji))
    (RingHom.ext fun _ => Subtype.ext rfl)
  have hi : i₀ ≤ i := hi₀j.trans hji

  let vi : (Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(V ⊓ (F j).toSubring)) :=
    Spec.map (CommRingCat.ofHom (levMap V (hF hji)))
  let Aᵢ : Scheme.{u} := pullback fⱼ vi
  let fᵢ : Aᵢ ⟶ Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)) := pullback.snd fⱼ vi
  let Lᵢ : RelativeGroupLaw ↥(V ⊓ (F i).toSubring) fᵢ := Lⱼ.baseChange vi
  have hLᵢ : Lᵢ.IsCommutative := hLⱼ.baseChange vi
  have hAᵢ : AbelianSchemePropertyBundle ↥(V ⊓ (F i).toSubring) fᵢ := hAⱼ' i hji

  let ui : (Spec (CommRingCat.of ↥(F i)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)) :=
    Spec.map (CommRingCat.ofHom (τ i))
  let wji : (Spec (CommRingCat.of ↥(F i)) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥(F j)) :=
    Spec.map (CommRingCat.ofHom (fldMap (hF hji)))
  have hτu : wji ≫ uj = ui ≫ vi := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => Subtype.ext ?_
    simp only [RingHom.comp_apply, fldMap_apply_coe, levMap_apply_coe, hτ]

  have hXw : (pullback.fst fX' wji ≫ pullback.fst fⱼ uj) ≫ fⱼ = (pullback.snd fX' wji ≫ ui) ≫ vi := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hτu,
      Category.assoc]
  let hX : pullback fX' wji ⟶ Aᵢ := pullback.lift (pullback.fst fX' wji ≫ pullback.fst fⱼ uj) (pullback.snd fX' wji ≫ ui) hXw
  have hX_fst : hX ≫ pullback.fst fⱼ vi = pullback.fst fX' wji ≫ pullback.fst fⱼ uj := pullback.lift_fst _ _ _
  have hX_snd : hX ≫ fᵢ = pullback.snd fX' wji ≫ ui := pullback.lift_snd _ _ _
  have hXpb : IsPullback hX (pullback.snd fX' wji) fᵢ ui := by
    refine IsPullback.of_right (h₁₂ := pullback.fst fⱼ vi) (h₂₂ := vi) ?_ hX_snd (IsPullback.of_hasPullback fⱼ vi)
    rw [hX_fst, ← hτu]
    exact (IsPullback.of_hasPullback fX' wji).paste_horiz (IsPullback.of_hasPullback fⱼ uj)

  have hXmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥(F i))) (x y : SchemeHomOver t (pullback.snd fX' wji)),
      ((LX'.baseChange wji).mul t x y).1 ≫ hX =
        (Lᵢ.mul (t ≫ ui) ⟨x.1 ≫ hX, by rw [Category.assoc, hXpb.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ hX, by rw [Category.assoc, hXpb.w, ← Category.assoc, y.2]⟩).1 := by
    intro T t x y
    apply pullback.hom_ext
    · rw [Category.assoc, hX_fst, ← Category.assoc, baseChange_mul_fst _ LX' t x y, baseChange_mul_fst _ Lⱼ]
      conv_rhs => rw [baseChange_mul_fst _ Lⱼ (t ≫ ui)]
      refine mul_val_congr Lⱼ ?_ _ _ _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hτu]
      · show (x.1 ≫ pullback.fst fX' wji) ≫ pullback.fst fⱼ uj = (x.1 ≫ hX) ≫ pullback.fst fⱼ vi
        rw [Category.assoc, Category.assoc, hX_fst]
      · show (y.1 ≫ pullback.fst fX' wji) ≫ pullback.fst fⱼ uj = (y.1 ≫ hX) ≫ pullback.fst fⱼ vi
        rw [Category.assoc, Category.assoc, hX_fst]
    · have h1 : (((LX'.baseChange wji).mul t x y).1 ≫ hX) ≫ fᵢ = t ≫ ui := by
        rw [Category.assoc, hX_snd, ← Category.assoc, ((LX'.baseChange wji).mul t x y).2]
      calc ((LX'.baseChange wji).mul t x y).1 ≫ hX ≫ pullback.snd fⱼ vi
          = (((LX'.baseChange wji).mul t x y).1 ≫ hX) ≫ fᵢ := (Category.assoc _ _ _).symm
        _ = t ≫ ui := h1
        _ = _ := ((Lᵢ.mul (t ≫ ui) _ _).2).symm

  have hι₀i : wji ≫ ι₀j = Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have sqPi := IsPullback.of_hasPullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom))
  have sqYi : IsPullback (pullback.fst fY' wji ≫ pullback.fst f₀ ι₀j) (pullback.snd fY' wji) f₀
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)) := by
    rw [← hι₀i]
    exact (IsPullback.of_hasPullback fY' wji).paste_horiz (IsPullback.of_hasPullback f₀ ι₀j)
  let dY : pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)) ≅
      pullback fY' wji := sqPi.isoIsPullback _ _ sqYi
  have hdY_fst : dY.hom ≫ pullback.fst fY' wji ≫ pullback.fst f₀ ι₀j = pullback.fst f₀ _ :=
    sqPi.isoIsPullback_hom_fst _ _ sqYi
  have hdY_snd : dY.hom ≫ pullback.snd fY' wji = pullback.snd f₀ _ := sqPi.isoIsPullback_hom_snd _ _ sqYi
  have hdYmul : IsHomOver (L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)))
      (LY'.baseChange wji) dY.hom hdY_snd := by
    intro T t x y
    have keyR : ∀ z : SchemeHomOver t (pullback.snd fY' wji),
        (z.1 ≫ pullback.fst fY' wji) ≫ pullback.snd f₀ ι₀j = t ≫ wji := fun z => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]
    have keyL : ∀ w : SchemeHomOver t
        (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom))),
        ((w.1 ≫ dY.hom) ≫ pullback.fst fY' wji) ≫ pullback.snd f₀ ι₀j = t ≫ wji := fun w => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, Category.assoc w.1, hdY_snd, w.2]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hdY_fst, baseChange_mul_fst _ L₀ t x y]
        conv_rhs => rw [Category.assoc, ← Category.assoc _ (pullback.fst fY' wji) (pullback.fst f₀ ι₀j),
          baseChange_mul_fst _ LY' t, baseChange_mul_fst _ L₀]
        refine mul_val_congr L₀ ?_ _ _ _ _ ?_ ?_
        · rw [Category.assoc, hι₀i]
        · show x.1 ≫ pullback.fst f₀ _ = ((x.1 ≫ dY.hom) ≫ pullback.fst fY' wji) ≫ pullback.fst f₀ ι₀j
          rw [Category.assoc, Category.assoc, hdY_fst]
        · show y.1 ≫ pullback.fst f₀ _ = ((y.1 ≫ dY.hom) ≫ pullback.fst fY' wji) ≫ pullback.fst f₀ ι₀j
          rw [Category.assoc, Category.assoc, hdY_fst]
      · exact (keyL _).trans (keyR _).symm
    · rw [Category.assoc, hdY_snd, ((L₀.baseChange _).mul t x y).2]
      exact (((LY'.baseChange wji).mul t _ _).2).symm

  have heᵢmul' : IsHomOver (LX'.baseChange wji) (LY'.baseChange wji) eᵢ.hom heᵢ := fun _ t x y => heᵢmul t x y
  have hd := IsHomOver.comp hdYmul (IsHomOver.inv eᵢ heᵢ heᵢmul')
  have hd_snd : (dY.hom ≫ eᵢ.inv) ≫ pullback.snd fX' wji = pullback.snd f₀ _ := by
    rw [Category.assoc, ← heᵢ, Iso.inv_hom_id_assoc, hdY_snd]

  refine ⟨i, hi, Aᵢ, fᵢ, Lᵢ, hLᵢ, hAᵢ, (dY.hom ≫ eᵢ.inv) ≫ hX, ?_, ?_⟩
  · have hsq : IsPullback (dY.hom ≫ eᵢ.inv) (pullback.snd f₀ _) (pullback.snd fX' wji) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hd_snd]⟩
    have := hsq.paste_horiz hXpb
    rwa [Category.id_comp] at this
  · intro T t x y
    rw [← Category.assoc, hd t x y, hXmul t]
    refine mul_val_congr Lᵢ rfl _ _ _ _ ?_ ?_
    · exact Category.assoc _ _ _
    · exact Category.assoc _ _ _

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.GoodReductionJacobian.RelativeGroupLaw.LimAB"

end S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso (solution)
