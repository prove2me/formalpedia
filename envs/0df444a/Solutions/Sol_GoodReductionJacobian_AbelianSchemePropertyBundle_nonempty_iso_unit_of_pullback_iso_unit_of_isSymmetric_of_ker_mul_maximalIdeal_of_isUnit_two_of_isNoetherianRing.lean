-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/91fef8b9-d0e6-5264-8cec-55cedab59119

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
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq"

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
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing.T3G1Kit"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing.T3G1Kit"

namespace T3PNeg
open GoodReductionJacobian

theorem negMor_comp_negMor {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) :
    negMor f L ≫ negMor f L = 𝟙 A := by
  letI := L.pointGroup f
  have h := T3G1Kit.inv_natural L f f (negMor f L) (negMor_over f L) (idPt f)
  have h1 : GoodReductionJacobian.schemeHomOverComp (negMor f L) (negMor_over f L) (idPt f) = L.inv f (idPt f) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact Category.comp_id _)
  rw [h1] at h
  have h2 : L.inv f (L.inv f (idPt f)) = idPt f := inv_inv (idPt f)
  have := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe, h2] at this
  exact this

scoped instance isIso_negMor {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) :
    IsIso (negMor f L) :=
  ⟨⟨negMor f L, negMor_comp_negMor f L, negMor_comp_negMor f L⟩⟩

end T3PNeg
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing.T3G1Kit P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing.T3PNeg"

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R₀] [Nontrivial R₀] [Algebra R R₁] [Algebra R R₀]
    (φ : R₁ →ₐ[R] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)
    (h2 : IsUnit (2 : R₁))

    (t : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
    (ht₁ : t ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))))
    (ht₂ : t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) =
          (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback t).obj M ≅ 𝟙_ _))
    (hsym : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁ M) :
    Nonempty (M ≅ 𝟙_ _) := by
  classical

  have hsq₁ : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) :=
    IsPullback.of_hasPullback _ _
  have hA₁ : AbelianSchemePropertyBundle R₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) :=
    hA.of_isPullback hsq₁
  haveI : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) := hA₁.proper
  haveI : IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) := inferInstance
  have FLAT : Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) := by
    haveI : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) := hA₁.smooth
    infer_instance
  haveI := FLAT
  have COMPACT : CompactSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) := by
    haveI : IsProper f := hA.proper
    infer_instance
  haveI := COMPACT

  have hφbase : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap R R₀)) := by
    have hφcomp : φ.toRingHom.comp (algebraMap R R₁) = algebraMap R R₀ := RingHom.ext fun r => φ.commutes r
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφcomp]
  have ht : IsPullback t (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    have big : IsPullback (t ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) f
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁))) := by
      rw [ht₁, hφbase]; exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right big ht₂ hsq₁
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := IsClosedImmersion.spec_of_surjective _ hφ
  haveI : IsClosedImmersion t := MorphismProperty.of_isPullback ht.flip inferInstance

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hi : IsPullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))
      (pullback.snd _ _) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) :=
    IsPullback.of_hasPullback _ _

  obtain ⟨σ⟩ := (AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) _ _).mp hsym

  have hneg : negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁ ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) = pullback.snd f _ := negMor_over _ L₁
  let n₀ := ht.lift (t ≫ negMor _ L₁) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀))))
    (by rw [Category.assoc, hneg, ht.w])
  have hn₀ : n₀ ≫ t = t ≫ negMor _ L₁ := ht.lift_fst _ _ _
  let nk := hi.lift (pullback.fst _ _ ≫ negMor _ L₁) (pullback.snd _ _) (by rw [Category.assoc, hneg, hi.w])
  have hnk : nk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ negMor _ L₁ := hi.lift_fst _ _ _
  have hnkf : nk ≫ pullback.snd _ _ = pullback.snd _ _ := hi.lift_snd _ _ _

  obtain ⟨𝒰₀, ⟨τ⟩⟩ := AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible (𝟙 _) M hM
  obtain ⟨e0⟩ := h0

  have hker_top : RingHom.ker φ.toRingHom ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ RingHom.ker φ.toRingHom := h ▸ trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hI : RingHom.ker φ.toRingHom ≤ IsLocalRing.maximalIdeal R₁ := IsLocalRing.le_maximalIdeal hker_top
  have hsmall' : RingHom.ker φ.toRingHom * IsLocalRing.maximalIdeal R₁ = ⊥ :=
    eq_bot_iff.mpr (Ideal.mul_le.mpr fun x hx m hm => by rw [hsmall x hx m hm]; exact Submodule.zero_mem _)
  let V : Submodule R₁ R₁ := RingHom.ker φ.toRingHom
  have hVtors : Module.IsTorsionBySet R₁ ↥V (IsLocalRing.maximalIdeal R₁ : Set R₁) := by
    rintro v ⟨m, hm⟩
    exact Subtype.ext (by simpa [mul_comm] using hsmall v.1 v.2 m hm)
  letI modV : Module (IsLocalRing.ResidueField R₁) ↥V := hVtors.module
  haveI : IsScalarTower R₁ (IsLocalRing.ResidueField R₁) ↥V := hVtors.isScalarTower
  haveI : Module.Finite R₁ ↥V := inferInstance
  haveI : Module.Finite (IsLocalRing.ResidueField R₁) ↥V :=
    Module.Finite.of_restrictScalars_finite R₁ (IsLocalRing.ResidueField R₁) ↥V
  have hιI : LinearMap.range V.subtype = Submodule.restrictScalars R₁ (RingHom.ker φ.toRingHom) := by
    rw [Submodule.range_subtype, Submodule.restrictScalars_self]

  obtain ⟨w, hw, hwcl⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_cechTrivialisation
      φ.toRingHom hφ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) t ht
      (pullback.snd _ _) (pullback.fst _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) hi
      (𝒰₀.comap (𝟙 _)) M τ e0

  let Lk := L₁.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))
  have homk : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R₁)))
      (P Q : SchemeHomOver t' (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))),
      (Lk.mul t' P Q).1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) =
        (L₁.mul (t' ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))
          ⟨P.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) L₁ t' P Q)
  have hnk' : negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) = pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁ :=
    T3G1Kit.negMor_comp L₁ Lk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) pullback.condition homk
  have hnkf' : negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk ≫ pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) = pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) := negMor_over _ Lk

  obtain ⟨𝒲, lam₁, lam₂, hlam₁, hlam₂⟩ := AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_preimage_preimage_of_isSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (𝒰₀.comap (𝟙 _)) (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁) (𝟙 _)
  have hlamk₁ : ∀ x, (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).U x ≤
      negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).U (lam₁ x) := by
    intro x
    show pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) ⁻¹ᵁ 𝒲.U x ≤ negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk ⁻¹ᵁ (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam₁ x)))
    rw [← Scheme.Hom.comp_preimage, hnk', Scheme.Hom.comp_preimage]
    exact fun p hp => hlam₁ x hp
  have hlamk₂ : ∀ x, (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).U x ≤
      (𝟙 (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).U (lam₂ x) := by
    intro x
    show pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) ⁻¹ᵁ 𝒲.U x ≤ (𝟙 (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) ⁻¹ᵁ (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))) ⁻¹ᵁ ((𝒰₀.comap (𝟙 _)).U (lam₂ x)))
    exact fun p hp => hlam₂ x hp

  have hJ : ∀ v w : ↥V, V.subtype v * V.subtype w = 0 := fun v w =>
    hsmall v.1 v.2 w.1 (hI w.2)
  obtain ⟨w₁, hw₁eq, hw₁⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) t t (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))
      (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁) (negMor_over _ L₁) n₀ hn₀ (negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk) hnk' hnkf'
      (𝒰₀.comap (𝟙 _)) 𝒲 lam₁ hlam₁ hlamk₁ M e0 w hw
  obtain ⟨w₂, hw₂eq, hw₂⟩ :=
    AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback ↥V V.subtype hJ
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) t t (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))
      (𝟙 _) (Category.id_comp _) (𝟙 _) (by simp) (𝟙 _) (by simp) (Category.id_comp _)
      (𝒰₀.comap (𝟙 _)) 𝒲 lam₂ hlam₂ hlamk₂ M e0 w hw
  have hw₁' := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso ↥V V.subtype (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) t 𝒲 σ _ w₁ hw₁
  have hw₂' := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso ↥V V.subtype (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) t 𝒲
    ((Scheme.Modules.pullbackId _).app M) _ w₂ hw₂

  let φN : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁)).obj M) ≅
      SheafOfModules.unit (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp t (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) L₁)).app M) ≪≫
      ((Scheme.Modules.pullbackCongr hn₀.symm).app M) ≪≫
      ((Scheme.Modules.pullbackComp n₀ t).app M).symm ≪≫
      (Scheme.Modules.pullback n₀).mapIso e0 ≪≫ Scheme.Modules.pullbackUnitIso n₀
  let φA : (Scheme.Modules.pullback t).obj M ≅
      SheafOfModules.unit (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).ringCatSheaf :=
    (Scheme.Modules.pullback t).mapIso σ.symm ≪≫ φN

  let φI : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback (𝟙 _)).obj M) ≅
      SheafOfModules.unit (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp t (𝟙 _)).app M) ≪≫
      ((Scheme.Modules.pullbackCongr (show (𝟙 _) ≫ t = t ≫ 𝟙 _ by simp).symm).app M) ≪≫
      ((Scheme.Modules.pullbackComp (𝟙 _) t).app M).symm ≪≫
      (Scheme.Modules.pullback (𝟙 _)).mapIso e0 ≪≫ Scheme.Modules.pullbackUnitIso (𝟙 _)
  let φB : (Scheme.Modules.pullback t).obj M ≅ SheafOfModules.unit (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).ringCatSheaf :=
    (Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullbackId _).app M).symm ≪≫ φI
  let ratio := (Scheme.Modules.pullbackUnitIso (⊤ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).Opens).ι).symm ≪≫
      (Scheme.Modules.pullback (⊤ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).Opens).ι).mapIso (φB.symm ≪≫ φA) ≪≫
      Scheme.Modules.pullbackUnitIso (⊤ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).Opens).ι
  have hsu : IsUnit (Scheme.Modules.unitAutSection ⊤ ratio) := by
    obtain ⟨hmul, hrefl⟩ := AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl (⊤ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))).Opens)
    refine IsUnit.of_mul_eq_one (b := Scheme.Modules.unitAutSection ⊤ ratio.symm) ?_
    rw [← hmul]
    convert hrefl using 2
    exact Iso.ext ratio.hom_inv_id
  have h₁bij := GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_specIso_inv_comp_appTop_of_isPullback
    hA (algebraMap R R₁) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) hsq₁
  have h₀bij := GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_specIso_inv_comp_appTop_of_isPullback
    hA (algebraMap R R₀) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) (pullback.fst f _) (IsPullback.of_hasPullback _ _)
  obtain ⟨u, hu1, hu⟩ := AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
    φ.toRingHom hφ hI (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) t ht.w h₁bij h₀bij _ hsu
  obtain ⟨u', huu'⟩ := hu1.exists_right_inv
  have hw₂'' := AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection ↥V V.subtype (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) t 𝒲 M φB φA u u' huu' hu w₂ hw₂'

  have hdiff := AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
      φ.toRingHom hφ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) t ht (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) hi 𝒲 M φA w₁ w₂ hw₁' hw₂''

  have hAk : AbelianSchemePropertyBundle (IsLocalRing.ResidueField R₁) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) := hA₁.of_isPullback hi
  have hsum : ∀ ξ, w₁ ξ + w₂ ξ ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).d (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) 0) := by
    intro ξ
    obtain ⟨b, hb⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
      (IsLocalRing.ResidueField R₁) (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) Lk hAk ((𝒰₀.comap (𝟙 _)).comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))))
      lam₁ lam₂ hlamk₁ hlamk₂ (w ξ) (hwcl ξ)
    rw [hw₁eq ξ, hw₂eq ξ]
    exact ⟨b, hb⟩

  have h2k : (2 : IsLocalRing.ResidueField R₁) ≠ 0 := by
    have h := h2.map (IsLocalRing.residue R₁)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hcob : ∀ ξ, w₂ ξ ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).d (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) 0) := by
    intro ξ
    have hm : (2 : IsLocalRing.ResidueField R₁) • w₂ ξ ∈
        LinearMap.range ((OModulePresheaf.unit (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))).d (𝒲.comap (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁))))) 0) := by
      have := Submodule.sub_mem _ (hsum ξ) (hdiff ξ)
      rwa [show w₁ ξ + w₂ ξ - (w₁ ξ - w₂ ξ) = (2 : IsLocalRing.ResidueField R₁) • w₂ ξ by rw [two_smul]; abel] at this
    have := Submodule.smul_mem _ (2 : IsLocalRing.ResidueField R₁)⁻¹ hm
    rwa [smul_smul, inv_mul_cancel₀ h2k, one_smul] at this

  exact AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
      φ.toRingHom hφ hsmall' hI ↥V V.subtype (Submodule.injective_subtype V) hιI
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₀)))) t ht (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R₁)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R₁)))) hi 𝒲 M φA w₂ hw₂'' hcob

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing (solution)
