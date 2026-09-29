-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0b37f31b-3e5e-5402-9223-92c61a9744d9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation
import Theorems.Thm_AlgebraicGeometry_SmallExtension_nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback
import Theorems.Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection
import Theorems.Thm_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec"
p2m_attr_erase "simp" "CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension"

universe u v

noncomputable section

namespace T3G1Kit

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

include hom in

theorem locIso_sliceAt_iff (hP : IsPullback u f' f ψ) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    {R : Type u} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) (x' : SchemeHomOver t' f') :
    LocIsoOnBase (pullback.snd f' t')
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)))
        (𝟙_ ((pullback f' t').Modules)) ↔
      LocIsoOnBase (pullback.snd f (t' ≫ ψ))
        ((Scheme.Modules.pullback (sliceAt f (pushAlong ψ u hu t' x'))).obj (mumfordBundle f L 𝓛))
        (𝟙_ ((pullback f (t' ≫ ψ)).Modules)) := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  let x : SchemeHomOver (t' ≫ ψ) f := pushAlong ψ u hu t' x'
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm

  let r : pullback f (t' ≫ ψ) ⟶ pullback f' t' :=
    pullback.lift
      (hP.lift (pullback.fst f (t' ≫ ψ)) (pullback.snd f (t' ≫ ψ) ≫ t')
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.snd f (t' ≫ ψ)) (by rw [IsPullback.lift_snd])
  let s : pullback f' t' ⟶ pullback f (t' ≫ ψ) :=
    pullback.lift (pullback.fst f' t' ≫ u) (pullback.snd f' t')
      (by rw [Category.assoc, hu, ← Category.assoc, pullback.condition, Category.assoc])
  have hr : r ≫ pullback.snd f' t' = pullback.snd f (t' ≫ ψ) ≫ 𝟙 _ := by
    simp only [r, pullback.lift_snd, Category.comp_id]
  have hs : s ≫ pullback.snd f (t' ≫ ψ) = pullback.snd f' t' ≫ 𝟙 _ := by
    simp only [s, pullback.lift_snd, Category.comp_id]
  have hslice_r : (r ≫ sliceAt f' x') ≫ pp = sliceAt f x := by
    apply pullback.hom_ext
    · simp only [r, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · simp only [r, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have hslice_s : s ≫ sliceAt f x = sliceAt f' x' ≫ pp := by
    apply pullback.hom_ext
    · simp only [s, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [s, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

  let I1r : (Scheme.Modules.pullback r).obj (𝟙_ (pullback f' t').Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso r
  let I2r : (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) :=
    (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso) ≪≫
      (Scheme.Modules.pullbackComp r (sliceAt f' x')).app _ ≪≫
        (Scheme.Modules.pullbackComp (r ≫ sliceAt f' x') pp).app _ ≪≫
          (Scheme.Modules.pullbackCongr hslice_r).app _

  let I1s : (Scheme.Modules.pullback s).obj (𝟙_ (pullback f (t' ≫ ψ)).Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso s
  let I2s : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) :=
    (Scheme.Modules.pullbackComp s (sliceAt f x)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice_s).app _ ≪≫
        ((Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _).symm ≪≫
          (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso.symm
  constructor
  · intro H'
    have Hr := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f' t') (pullback.snd f (t' ≫ ψ)) r (𝟙 _) hr H'
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2r.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hr (locIsoOnBase_of_iso _ I1r))
  · intro H
    have Hs := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f (t' ≫ ψ)) (pullback.snd f' t') s (𝟙 _) hs H
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2s.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hs (locIsoOnBase_of_iso _ I1s))

include hom in

theorem mul_self_eq_one_iff (hP : IsPullback u f' f ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (x' : SchemeHomOver t' f') :
    L'.mul t' x' x' = L'.one t' ↔
      L.mul (t' ≫ ψ) (pushAlong ψ u hu t' x') (pushAlong ψ u hu t' x') = L.one (t' ≫ ψ) := by
  constructor
  · intro h
    rw [← pushAlong_mul L L' ψ u hu hom, h, pushAlong_one L L' ψ u hu hom]
  · intro h
    apply Subtype.ext
    apply hP.hom_ext
    · rw [one_val_comp L L' ψ u hu hom t']
      exact (hom T t' x' x').trans (congrArg Subtype.val h)
    · rw [(L'.mul t' x' x').2, (L'.one t').2]

include hom in

theorem kernelTrivial_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hker : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x' H'
  have hx : pushAlong ψ u hu t' x' = L.one (t' ≫ ψ) :=
    hker R (t' ≫ ψ) (pushAlong ψ u hu t' x') ((locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x').1 H')
  apply Subtype.ext
  apply hP.hom_ext
  · rw [one_val_comp L L' ψ u hu hom t']
    exact congrArg Subtype.val hx
  · rw [x'.2, (L'.one t').2]

include hom in

theorem kernelIsTwoTorsion_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x'
  rw [locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x', hK R (t' ≫ ψ) (pushAlong ψ u hu t' x'),
    mul_self_eq_one_iff L L' ψ u hu hom hP t' x']

include hom in
theorem rosatiCompatible_of_comm {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b : I, act b ≫ f = f)
    (act' : I → (A' ⟶ A')) (act'_over : ∀ b : I, act' b ≫ f' = f') (hact : ∀ b : I, act' b ≫ u = u ≫ act b)
    (star : I → I) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    (hros : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f' L' ((Scheme.Modules.pullback u).obj 𝓛) act' act'_over star := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  intro b
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have comm : pp ≫ (pullback.fst f f ≫ f) = (pullback.fst f' f' ≫ f') ≫ ψ := by
    simp only [pp, Category.assoc, pullback.lift_fst_assoc, hu]
  have H := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    (g := pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') pp ψ comm (hros b)

  let m : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let m' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b)
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  let n : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
      (by rw [Category.assoc, act_over]; exact pullback.condition)
  let n' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f')
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  have hm : m' ≫ pp = pp ≫ m := by
    apply pullback.hom_ext
    · simp only [m, m', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [m, m', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hact]
  have hn : n' ≫ pp = pp ≫ n := by
    apply pullback.hom_ext
    · simp only [n, n', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hact]
    · simp only [n, n', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  let Im : (Scheme.Modules.pullback m').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback m).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback m').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp m' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hm).app _ ≪≫ ((Scheme.Modules.pullbackComp pp m).app _).symm
  let In : (Scheme.Modules.pullback n').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback n).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback n').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp n' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hn).app _ ≪≫ ((Scheme.Modules.pullbackComp pp n).app _).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ Im)
    ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans H (locIsoOnBase_of_iso _ In.symm))

include hom in

theorem isSymmetric_of_comm (𝓛 : A.Modules) (hs : IsSymmetric f L 𝓛) :
    IsSymmetric f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  have h1 : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛))
      ((Scheme.Modules.pullback u).obj 𝓛) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu hs
  have e : (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom)).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans (locIsoOnBase_of_iso f' e) h1

include hom in

theorem root_transport (hP : IsPullback u f' f ψ) (M 𝓛₀ : A.Modules) (h0inv : Scheme.Modules.IsInvertible 𝓛₀)
    (h0ker : KernelTrivial f L 𝓛₀)
    (h0loc : LocIsoOnBase f M (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
        ((Scheme.Modules.pullback u).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛₀)) := by
  refine ⟨h0inv.pullback u, kernelTrivial_of_isPullback L L' ψ u hu hom hP 𝓛₀ h0inv h0ker, ?_⟩
  have H : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
      ((Scheme.Modules.pullback u).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu h0loc
  refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans H (locIsoOnBase_of_iso f' ?_)
  exact Scheme.Modules.pullbackTensorObjIso u _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛₀ ≪≫
        (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom).symm).app 𝓛₀ ≪≫
        ((Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛₀).symm)

end Hom

end T3G1Kit
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.T3G1Kit"

namespace P2N12

noncomputable def dualIso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm
end P2N12
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.T3G1Kit"

theorem solution
    {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [IsNoetherianRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hK : RingHom.ker (algebraMap B₁ B₀) * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    (hKm : IsLocalRing.maximalIdeal B₁ * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B₁)}
    (L : RelativeGroupLaw B₁ f) (hA : AbelianSchemePropertyBundle B₁ f)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t' f₀),
      (L₀.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (M M' : (pullback f f).Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')

    (h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M'))

    (h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M ≅ 𝟙_ _))
    (h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M) ≅ 𝟙_ _))
    (h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M' ≅ 𝟙_ _))
    (h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M') ≅ 𝟙_ _)) :
    Nonempty (M ≅ M') := by
  classical

  let π : B₁ →+* B₀ := algebraMap B₁ B₀
  let X := pullback f f
  let F : X ⟶ Spec (CommRingCat.of B₁) := pullback.fst f f ≫ f
  let X₀ := pullback f₀ f₀
  let F₀ : X₀ ⟶ Spec (CommRingCat.of B₀) := pullback.fst f₀ f₀ ≫ f₀
  let gg : X₀ ⟶ X := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc])
  let rk := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B₁))
  let Ak := pullback f rk
  let gk : Ak ⟶ A := pullback.fst f rk
  let fk : Ak ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) := pullback.snd f rk
  have hAk_sq : IsPullback gk fk f rk := IsPullback.of_hasPullback _ _
  let Xk := pullback fk fk
  let Fk : Xk ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) := pullback.fst fk fk ≫ fk
  let ii : Xk ⟶ X := pullback.lift (pullback.fst fk fk ≫ gk) (pullback.snd fk fk ≫ gk)
    (by rw [Category.assoc, Category.assoc, hAk_sq.w, ← Category.assoc, pullback.condition, Category.assoc])

  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : IsSeparated f := inferInstance
  haveI : Flat f := inferInstance
  haveI : IsSeparated F := inferInstance
  haveI : Flat F := inferInstance
  haveI : CompactSpace ↥A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)

  have prodCart : ∀ {S' : Scheme.{0}} {A' : Scheme.{0}} (f' : A' ⟶ S') (u : A' ⟶ A) (s : S' ⟶ Spec (CommRingCat.of B₁))
      (hu : IsPullback u f' f s) (uu : pullback f' f' ⟶ X) (h1 : uu ≫ pullback.fst f f = pullback.fst f' f' ≫ u)
      (h2 : uu ≫ pullback.snd f f = pullback.snd f' f' ≫ u),
      IsPullback uu (pullback.fst f' f' ≫ f') F s := by
    intro S' A' f' u s hu uu h1 h2
    have sq₀ : IsPullback (pullback.snd f' f') (pullback.fst f' f') f' f' := (IsPullback.of_hasPullback _ _).flip
    have sqX : IsPullback (pullback.snd f f) (pullback.fst f f) f f := (IsPullback.of_hasPullback _ _).flip
    have O : IsPullback (uu ≫ pullback.snd f f) (pullback.fst f' f') f (u ≫ f) := by
      rw [h2, hu.w]; exact sq₀.paste_horiz hu
    have hq : IsPullback uu (pullback.fst f' f') (pullback.fst f f) u := IsPullback.of_right O h1 sqX
    exact hq.paste_vert hu
  have hgg : IsPullback gg F₀ F (Spec.map (CommRingCat.ofHom π)) :=
    prodCart f₀ g _ hg gg (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hii : IsPullback ii Fk F rk :=
    prodCart fk gk rk hAk_sq ii (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion gg := MorphismProperty.of_isPullback hgg.flip inferInstance
  haveI : IsClosedImmersion rk := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion ii := MorphismProperty.of_isPullback hii.flip inferInstance
  haveI : IsClosedImmersion gk := MorphismProperty.of_isPullback hAk_sq.flip inferInstance
  haveI : IsClosedImmersion g := MorphismProperty.of_isPullback hg.flip inferInstance
  have hAk : AbelianSchemePropertyBundle (IsLocalRing.ResidueField B₁) fk := hA.of_isPullback hAk_sq

  have hker_top : RingHom.ker π ≠ ⊤ := by
    intro h
    have h1 : (1 : B₁) ∈ RingHom.ker π * RingHom.ker π := by
      simpa only [h, Ideal.top_mul] using (Submodule.mem_top : (1 : B₁) ∈ (⊤ : Ideal B₁))
    rw [hK] at h1
    exact one_ne_zero ((Submodule.mem_bot B₁).mp h1)
  have hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁ := IsLocalRing.le_maximalIdeal hker_top
  have hsmall' : RingHom.ker π * IsLocalRing.maximalIdeal B₁ = ⊥ := by rw [mul_comm]; exact hKm
  let V : Submodule B₁ B₁ := RingHom.ker π
  have hVtors : Module.IsTorsionBySet B₁ ↥V (IsLocalRing.maximalIdeal B₁ : Set B₁) := by
    rintro v ⟨m, hm⟩
    refine Subtype.ext ?_
    have : m * (v : B₁) ∈ IsLocalRing.maximalIdeal B₁ * RingHom.ker π := Ideal.mul_mem_mul hm v.2
    rw [hKm] at this
    simpa [smul_eq_mul, mul_comm] using (Submodule.mem_bot B₁).mp this
  letI modV : Module (IsLocalRing.ResidueField B₁) ↥V := hVtors.module
  haveI : IsScalarTower B₁ (IsLocalRing.ResidueField B₁) ↥V := hVtors.isScalarTower
  haveI : Module.Finite B₁ ↥V := inferInstance
  haveI : Module.Finite (IsLocalRing.ResidueField B₁) ↥V :=
    Module.Finite.of_restrictScalars_finite B₁ (IsLocalRing.ResidueField B₁) ↥V
  have hιI : LinearMap.range V.subtype = Submodule.restrictScalars B₁ (RingHom.ker π) := by
    rw [Submodule.range_subtype, Submodule.restrictScalars_self]
  have hJ : ∀ v w : ↥V, V.subtype v * V.subtype w = 0 := by
    intro v w
    have : (v : B₁) * (w : B₁) ∈ RingHom.ker π * RingHom.ker π := Ideal.mul_mem_mul v.2 w.2
    rw [hK] at this
    exact (Submodule.mem_bot B₁).mp this

  let N : X.Modules := M ⊗ Scheme.Modules.dual M'
  have hN : Scheme.Modules.IsInvertible N :=
    hM.tensor_monoidalV2 (Scheme.Modules.IsInvertible.dual_monoidalV2 hM').1
  obtain ⟨e0⟩ := h0
  let φ₀ : (Scheme.Modules.pullback gg).obj N ≅ SheafOfModules.unit X₀.ringCatSheaf :=
    Scheme.Modules.pullbackTensorObjIso gg M (Scheme.Modules.dual M') ≪≫
      whiskerLeftIso _ ((Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 gg hM').some ≪≫
        (P2N12.dualIso e0).symm) ≪≫
      (Scheme.Modules.IsInvertible.dual_monoidalV2 (hM.pullback gg)).2.some

  obtain ⟨𝒰₀, ⟨τ⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible (𝟙 X) N hN
  obtain ⟨w, hw, hwcl⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_cechTrivialisation
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI
      F F₀ gg hgg Fk ii hii (𝒰₀.comap (𝟙 _)) N τ φ₀

  let e₁ : Spec (CommRingCat.of B₁) ⟶ A := (L.one (𝟙 _)).1
  have he₁ : e₁ ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  let e₀ : Spec (CommRingCat.of B₀) ⟶ A₀ := (L₀.one (𝟙 _)).1
  have he₀ : e₀ ≫ f₀ = 𝟙 _ := (L₀.one (𝟙 _)).2
  let Lk := L.baseChange rk
  let ek : Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)) ⟶ Ak := (Lk.one (𝟙 _)).1
  have hek : ek ≫ fk = 𝟙 _ := (Lk.one (𝟙 _)).2

  have homk : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField B₁)))
      (P Q : SchemeHomOver t' fk),
      (Lk.mul t' P Q).1 ≫ gk =
        (L.mul (t' ≫ rk) ⟨P.1 ≫ gk, by rw [Category.assoc, hAk_sq.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gk, by rw [Category.assoc, hAk_sq.w, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul rk L t' P Q)
  have he₀g : e₀ ≫ g = Spec.map (CommRingCat.ofHom π) ≫ e₁ := by
    have h1 := T3G1Kit.one_val_comp L L₀ (Spec.map (CommRingCat.ofHom π)) g hg.w (fun T t' P Q => hg_mul t' P Q) (𝟙 _)
    have h2 := congrArg Subtype.val
      (L.one_natural (𝟙 _) ((𝟙 _) ≫ Spec.map (CommRingCat.ofHom π)) (Spec.map (CommRingCat.ofHom π)) (by simp))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    exact h1.trans h2.symm
  have hekg : ek ≫ gk = rk ≫ e₁ := by
    have h1 := T3G1Kit.one_val_comp L Lk rk gk hAk_sq.w homk (𝟙 _)
    have h2 := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 _) ≫ rk) rk (by simp))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    exact h1.trans h2.symm
  let s₁ : A ⟶ X := pullback.lift (𝟙 A) (f ≫ e₁) (by simp [he₁])
  let s₂ : A ⟶ X := pullback.lift (f ≫ e₁) (𝟙 A) (by simp [he₁])
  let s0₁ : A₀ ⟶ X₀ := pullback.lift (𝟙 A₀) (f₀ ≫ e₀) (by simp [he₀])
  let s0₂ : A₀ ⟶ X₀ := pullback.lift (f₀ ≫ e₀) (𝟙 A₀) (by simp [he₀])
  let sk₁ : Ak ⟶ Xk := pullback.lift (𝟙 Ak) (fk ≫ ek) (by simp [hek])
  let sk₂ : Ak ⟶ Xk := pullback.lift (fk ≫ ek) (𝟙 Ak) (by simp [hek])
  have s₁f : s₁ ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have s₁s : s₁ ≫ pullback.snd f f = f ≫ e₁ := pullback.lift_snd _ _ _
  have s₂f : s₂ ≫ pullback.fst f f = f ≫ e₁ := pullback.lift_fst _ _ _
  have s₂s : s₂ ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
  have s0₁f : s0₁ ≫ pullback.fst f₀ f₀ = 𝟙 A₀ := pullback.lift_fst _ _ _
  have s0₁s : s0₁ ≫ pullback.snd f₀ f₀ = f₀ ≫ e₀ := pullback.lift_snd _ _ _
  have s0₂f : s0₂ ≫ pullback.fst f₀ f₀ = f₀ ≫ e₀ := pullback.lift_fst _ _ _
  have s0₂s : s0₂ ≫ pullback.snd f₀ f₀ = 𝟙 A₀ := pullback.lift_snd _ _ _
  have sk₁f : sk₁ ≫ pullback.fst fk fk = 𝟙 Ak := pullback.lift_fst _ _ _
  have sk₁s : sk₁ ≫ pullback.snd fk fk = fk ≫ ek := pullback.lift_snd _ _ _
  have sk₂f : sk₂ ≫ pullback.fst fk fk = fk ≫ ek := pullback.lift_fst _ _ _
  have sk₂s : sk₂ ≫ pullback.snd fk fk = 𝟙 Ak := pullback.lift_snd _ _ _
  have ggf : gg ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g := pullback.lift_fst _ _ _
  have ggs : gg ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g := pullback.lift_snd _ _ _
  have iif : ii ≫ pullback.fst f f = pullback.fst fk fk ≫ gk := pullback.lift_fst _ _ _
  have iis : ii ≫ pullback.snd f f = pullback.snd fk fk ≫ gk := pullback.lift_snd _ _ _
  have hs₁F : s₁ ≫ F = f := by
    show s₁ ≫ pullback.fst f f ≫ f = f
    rw [← Category.assoc, s₁f, Category.id_comp]
  have hs₂F : s₂ ≫ F = f := by
    show s₂ ≫ pullback.fst f f ≫ f = f
    rw [← Category.assoc, s₂f, Category.assoc, he₁, Category.comp_id]
  have hs0₁ : s0₁ ≫ gg = g ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ggf, ← Category.assoc, s0₁f, Category.id_comp, Category.assoc, s₁f, Category.comp_id]
    · rw [Category.assoc, ggs, ← Category.assoc, s0₁s, Category.assoc, he₀g, ← Category.assoc, ← hg.w]
      simp only [Category.assoc, s₁s]
  have hs0₂ : s0₂ ≫ gg = g ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ggf, ← Category.assoc, s0₂f, Category.assoc, he₀g, ← Category.assoc, ← hg.w]
      simp only [Category.assoc, s₂f]
    · rw [Category.assoc, ggs, ← Category.assoc, s0₂s, Category.id_comp, Category.assoc, s₂s, Category.comp_id]
  have hsk₁ : sk₁ ≫ ii = gk ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, iif, ← Category.assoc, sk₁f, Category.id_comp, Category.assoc, s₁f, Category.comp_id]
    · rw [Category.assoc, iis, ← Category.assoc, sk₁s, Category.assoc, hekg, ← Category.assoc, ← hAk_sq.w]
      simp only [Category.assoc, s₁s]
  have hsk₂ : sk₂ ≫ ii = gk ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, iif, ← Category.assoc, sk₂f, Category.assoc, hekg, ← Category.assoc, ← hAk_sq.w]
      simp only [Category.assoc, s₂f]
    · rw [Category.assoc, iis, ← Category.assoc, sk₂s, Category.id_comp, Category.assoc, s₂s, Category.comp_id]
  have hsk₁F : sk₁ ≫ Fk = fk := by
    show sk₁ ≫ pullback.fst fk fk ≫ fk = fk
    rw [← Category.assoc, sk₁f, Category.id_comp]
  have hsk₂F : sk₂ ≫ Fk = fk := by
    show sk₂ ≫ pullback.fst fk fk ≫ fk = fk
    rw [← Category.assoc, sk₂f, Category.assoc, hek, Category.comp_id]

  obtain ⟨𝒱, lam, hlam⟩ := AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    (fun _ : Fin 2 => X) (fun j => if j = 0 then s₁ else s₂) (fun _ => 𝒰₀.comap (𝟙 _))
  have hlam₁ : ∀ v, 𝒱.U v ≤ s₁ ⁻¹ᵁ (𝒰₀.comap (𝟙 _)).U (lam 0 v) := fun v => by simpa using hlam 0 v
  have hlam₂ : ∀ v, 𝒱.U v ≤ s₂ ⁻¹ᵁ (𝒰₀.comap (𝟙 _)).U (lam 1 v) := fun v => by simpa using hlam 1 v
  have hlamk₁ : ∀ v, (𝒱.comap gk).U v ≤ sk₁ ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap ii).U (lam 0 v) := by
    intro v
    show gk ⁻¹ᵁ 𝒱.U v ≤ sk₁ ⁻¹ᵁ (ii ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam 0 v)))
    rw [← Scheme.Hom.comp_preimage, hsk₁, Scheme.Hom.comp_preimage]
    exact fun p hp => hlam₁ v hp
  have hlamk₂ : ∀ v, (𝒱.comap gk).U v ≤ sk₂ ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap ii).U (lam 1 v) := by
    intro v
    show gk ⁻¹ᵁ 𝒱.U v ≤ sk₂ ⁻¹ᵁ (ii ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam 1 v)))
    rw [← Scheme.Hom.comp_preimage, hsk₂, Scheme.Hom.comp_preimage]
    exact fun p hp => hlam₂ v hp

  obtain ⟨w₁, hw₁eq, hw₁⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      F f gg g Fk fk ii gk s₁ hs₁F s0₁ hs0₁ sk₁ hsk₁ hsk₁F (𝒰₀.comap (𝟙 _)) 𝒱 (lam 0) hlam₁ hlamk₁ N φ₀ w hw
  obtain ⟨w₂, hw₂eq, hw₂⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      F f gg g Fk fk ii gk s₂ hs₂F s0₂ hs0₂ sk₂ hsk₂ hsk₂F (𝒰₀.comap (𝟙 _)) 𝒱 (lam 1) hlam₂ hlamk₂ N φ₀ w hw

  let φ := pullback.fst f (𝟙 (Spec (CommRingCat.of B₁)))
  have hφ : pullback.snd f (𝟙 (Spec (CommRingCat.of B₁))) = φ ≫ f := by
    have := pullback.condition (f := f) (g := 𝟙 (Spec (CommRingCat.of B₁)))
    rw [Category.comp_id] at this
    exact this.symm
  have hsl₁ : sliceAt f (L.one (𝟙 _)) = φ ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, s₁f, Category.comp_id]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, s₁s, ← Category.assoc, ← hφ]; exact pullback.lift_snd _ _ _
  have hsl₂ : sliceAt f (L.one (𝟙 _)) ≫ (pullbackSymmetry f f).hom = φ ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, Category.assoc, s₂f, ← Category.assoc, ← hφ]
      exact pullback.lift_snd _ _ _
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, Category.assoc, s₂s, Category.comp_id]
      exact pullback.lift_fst _ _ _
  have bridge : ∀ (t : pullback f (𝟙 (Spec (CommRingCat.of B₁))) ⟶ X) (s : A ⟶ X) (hts : t = φ ≫ s) (P : X.Modules)
      (e : (Scheme.Modules.pullback t).obj P ≅ 𝟙_ _), Nonempty ((Scheme.Modules.pullback s).obj P ≅ 𝟙_ A.Modules) := by
    intro t s hts P e
    have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback s).obj P) ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackComp φ s).app P ≪≫ (Scheme.Modules.pullbackCongr hts.symm).app P ≪≫ e
    let back : ∀ Q : A.Modules, (Scheme.Modules.pullback (inv φ)).obj ((Scheme.Modules.pullback φ).obj Q) ≅ Q := fun Q =>
      (Scheme.Modules.pullbackComp (inv φ) φ).app Q ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app Q ≪≫
        (Scheme.Modules.pullbackId A).app Q
    exact ⟨(back _).symm ≪≫ (Scheme.Modules.pullback (inv φ)).mapIso e1 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso (inv φ)⟩
  have trivN : ∀ (s : A ⟶ X) (a : (Scheme.Modules.pullback s).obj M ≅ 𝟙_ _) (b : (Scheme.Modules.pullback s).obj M' ≅ 𝟙_ _),
      (Scheme.Modules.pullback s).obj N ≅ SheafOfModules.unit A.ringCatSheaf := fun s a b =>
    Scheme.Modules.pullbackTensorObjIso s M (Scheme.Modules.dual M') ≪≫
      (a ⊗ᵢ ((Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 s hM').some ≪≫ P2N12.dualIso b)) ≪≫
      (Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.isInvertible_unit A)).2.some
  obtain ⟨a₁⟩ := bridge _ s₁ hsl₁ M h1.some
  obtain ⟨b₁⟩ := bridge _ s₁ hsl₁ M' h1'.some
  obtain ⟨a₂⟩ := bridge _ s₂ hsl₂ M
    (((Scheme.Modules.pullbackComp (sliceAt f (L.one (𝟙 _))) (pullbackSymmetry f f).hom).app M).symm ≪≫ h2.some)
  obtain ⟨b₂⟩ := bridge _ s₂ hsl₂ M'
    (((Scheme.Modules.pullbackComp (sliceAt f (L.one (𝟙 _))) (pullbackSymmetry f f).hom).app M').symm ≪≫ h2'.some)
  have ε₁ : (Scheme.Modules.pullback s₁).obj N ≅ SheafOfModules.unit A.ringCatSheaf := trivN s₁ a₁ b₁
  have ε₂ : (Scheme.Modules.pullback s₂).obj N ≅ SheafOfModules.unit A.ringCatSheaf := trivN s₂ a₂ b₂

  have hH1 : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom := by
    have hsq : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id B₁))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact hA.bijective_specIso_inv_comp_appTop_of_isPullback (RingHom.id B₁) f (𝟙 A) hsq
  have hH0 : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom :=
    hA.bijective_specIso_inv_comp_appTop_of_isPullback π f₀ g hg
  obtain ⟨uas_trans, uas_refl⟩ := AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl (Y := A₀) ⊤

  have hcob : ∀ (s : A ⟶ X) (ε : (Scheme.Modules.pullback s).obj N ≅ SheafOfModules.unit A.ringCatSheaf)
      (φ' : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj N) ≅ SheafOfModules.unit A₀.ringCatSheaf)
      (w' : Module.Dual (IsLocalRing.ResidueField B₁) ↥V →ₗ[IsLocalRing.ResidueField B₁]
        (OModulePresheaf.unit fk).cochain (𝒱.comap gk) 1)
      (hw' : IsPicDeformationCocycle ↥V V.subtype f fk gk g 𝒱 ((Scheme.Modules.pullback s).obj N) φ' w'),
      ∀ ξ, w' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒱.comap gk) 0) := by
    intro s ε φ' w' hw' ξ

    have h7 := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso ↥V V.subtype f fk gk g 𝒱 ε φ' w' hw'
    let ψ := (Scheme.Modules.pullback g).mapIso ε.symm ≪≫ φ'
    let φc := Scheme.Modules.pullbackUnitIso g
    let δ := (Scheme.Modules.pullbackUnitIso (⊤ : A₀.Opens).ι).symm ≪≫
      (Scheme.Modules.pullback (⊤ : A₀.Opens).ι).mapIso (ψ.symm ≪≫ φc) ≪≫ Scheme.Modules.pullbackUnitIso (⊤ : A₀.Opens).ι
    have hδu : IsUnit (Scheme.Modules.unitAutSection ⊤ δ) := by
      refine IsUnit.of_mul_eq_one (b := Scheme.Modules.unitAutSection ⊤ δ.symm) ?_
      rw [← uas_trans]
      convert uas_refl using 2
      exact Iso.self_symm_id δ
    obtain ⟨u, hu, hgu⟩ := AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
      π hπ hI f f₀ g hg.w hH1 hH0 _ hδu
    have h8 := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection ↥V V.subtype f fk gk g 𝒱
      (SheafOfModules.unit A.ringCatSheaf) ψ φc u (↑hu.unit⁻¹ : Γ(A, ⊤)) hu.mul_val_inv hgu w' h7

    have h0' := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero ↥V V.subtype f fk gk g 𝒱
    have hd := AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI f f₀ g hg fk gk hAk_sq 𝒱 _ _ w' 0 h8 h0' ξ
    simpa using hd
  have hc₁ := hcob s₁ ε₁ _ w₁ hw₁
  have hc₂ := hcob s₂ ε₂ _ w₂ hw₂

  have hKun : ∀ ξ, w ξ ∈ LinearMap.range ((OModulePresheaf.unit Fk).d ((𝒰₀.comap (𝟙 _)).comap ii) 0) := by
    intro ξ
    refine GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
      (IsLocalRing.ResidueField B₁) fk hAk ek hek sk₁ sk₂ sk₁f sk₁s sk₂f sk₂s ((𝒰₀.comap (𝟙 _)).comap ii) (𝒱.comap gk) (𝒱.comap gk)
      (lam 0) (lam 1) hlamk₁ hlamk₂ (w ξ) (hwcl ξ) ?_ ?_
    · rw [← hw₁eq ξ]; exact hc₁ ξ
    · rw [← hw₂eq ξ]; exact hc₂ ξ

  obtain ⟨eN⟩ := AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
      π hπ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI F F₀ gg hgg Fk ii hii (𝒰₀.comap (𝟙 _)) N φ₀ w hw hKun
  have eMM' : Scheme.Modules.dual M' ⊗ M' ≅ 𝟙_ X.Modules :=
    β_ _ _ ≪≫ (Scheme.Modules.IsInvertible.dual_monoidalV2 hM').2.some
  exact ⟨(ρ_ M).symm ≪≫ whiskerLeftIso M eMM'.symm ≪≫ (α_ M (Scheme.Modules.dual M') M').symm ≪≫
    whiskerRightIso eN M' ≪≫ λ_ M'⟩

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing (solution)
