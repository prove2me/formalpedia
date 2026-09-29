-- Prove2me | solution 1 for NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/436a9b4c-f564-52da-bb66-dfad08efd071

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace R4W3GDEngine

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable abbrev sMap : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

theorem covering_props [Module.FaithfullyFlat R R'] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (sMap R R') := by
  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat := by
    change (algebraMap R R').FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨hfl, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).2 hff
  exact ⟨⟨hsurj, hfl⟩, inferInstance⟩

scoped instance surjective_sMap [Module.FaithfullyFlat R R'] : Surjective (sMap R R') :=
  (covering_props R R').1.1

scoped instance flat_sMap [Module.FaithfullyFlat R R'] : Flat (sMap R R') :=
  (covering_props R R').1.2

theorem props_descend [Module.FaithfullyFlat R R']
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R))
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R'))
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R')) :
    Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g := by
  have hQ := covering_props R R'
  have hsnd : pullback.snd g (sMap R R') = e.hom ≫ g' := he.symm
  have hSm : Smooth (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have hSep : IsSeparated (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have hLoft : LocallyOfFiniteType (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have hQc : QuasiCompact (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ hSm
  · haveI := AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsSeparated)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ hSep
  · exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ hLoft
  ·

    haveI : CompactSpace ↥B' := QuasiCompact.compactSpace_of_compactSpace g'
    haveI : CompactSpace ↥(pullback g (sMap R R')) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).symm.compactSpace
    have hsurj : Function.Surjective (pullback.fst g (sMap R R')).base :=
      (inferInstance : Surjective (pullback.fst g (sMap R R'))).surj
    haveI : CompactSpace ↥B := ⟨by
      rw [← hsurj.range_eq]
      exact isCompact_range (pullback.fst g (sMap R R')).base.hom.continuous⟩
    exact HasAffineProperty.iff_of_isAffine.mpr ‹CompactSpace ↥B›

variable {R R'}

noncomputable def pointBC {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    SchemeHomOver (pullback.snd t (sMap R R')) (pullback.snd g (sMap R R')) :=
  ⟨pullback.map t (sMap R R') g (sMap R R') x.1 (𝟙 _) (𝟙 _) (by rw [x.2, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp]),
    by rw [pullback.lift_snd, Category.comp_id]⟩

@[scoped simp]
theorem pointBC_coe_fst {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC g x).1 ≫ pullback.fst g (sMap R R') = pullback.fst t (sMap R R') ≫ x.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem pointBC_coe_snd {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC g x).1 ≫ pullback.snd g (sMap R R') = pullback.snd t (sMap R R') := by
  rw [(pointBC g x).2]

theorem pointBC_natural {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    pointBC g (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map t' (sMap R R') t (sMap R R') ψ (𝟙 _) (𝟙 _) (by rw [hψ, Category.comp_id])
          (by rw [Category.comp_id, Category.id_comp]))
        (by rw [pullback.lift_snd, Category.comp_id]) (pointBC g x) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, pointBC_coe_fst,
      pullback.lift_fst_assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, pointBC_coe_snd,
      pullback.lift_snd, Category.comp_id]

theorem pointBC_injective [Module.FaithfullyFlat R R'] {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (pointBC (R' := R') g (t := t)) := by
  intro x y hxy
  have h := congrArg (fun z => z.1 ≫ pullback.fst g (sMap R R')) hxy
  simp only [pointBC_coe_fst] at h
  haveI : QuasiCompact (pullback.fst t (sMap R R')) := inferInstance
  haveI : Epi (pullback.fst t (sMap R R')) := inferInstance
  exact Subtype.ext ((cancel_epi (pullback.fst t (sMap R R'))).1 h)

section Invariant

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g')

noncomputable def yRel {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ pullback (g' ≫ sMap R R') (sMap R R') :=
  pullback.map _ _ _ _ y.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, y.2])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem yRel_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yRel y ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem yRel_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yRel y ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def Invariant {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : Prop :=
  DescentAction.flipMap (sMap R R') t ≫ y.1 = yRel y ≫ A.act

variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))

noncomputable def pointBC' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    SchemeHomOver (pullback.snd t (sMap R R')) g' :=
  NeronModelInfra.schemeHomOverComp (pointBC g x) ⟨e.hom, he⟩

@[scoped simp]
theorem pointBC'_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC' e he x).1 = (pointBC g x).1 ≫ e.hom :=
  rfl

theorem pointBC'_injective [Module.FaithfullyFlat R R'] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (pointBC' e he (t := t)) := by
  intro x₁ x₂ h
  have h' : (pointBC g x₁).1 ≫ e.hom = (pointBC g x₂).1 ≫ e.hom := congrArg Subtype.val h
  exact pointBC_injective g t (Subtype.ext ((cancel_mono e.hom).1 h'))

theorem invariant_pointBC'
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    Invariant A (pointBC' e he x) := by

  let xSS : pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶
      pullback (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.map _ _ _ _ (pointBC g x).1 (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Category.assoc, (pointBC g x).2]) (by rw [Category.comp_id, Category.id_comp])
  have hxSS₁ : xSS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (pointBC g x).1 := pullback.lift_fst _ _ _
  have hxSS₂ : xSS ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

  have hrel : yRel (pointBC' e he x) =
      xSS ≫ pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [yRel_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hxSS₁, Category.assoc]
      rfl
    · rw [yRel_snd, Category.assoc, pullback.lift_snd, Category.comp_id, hxSS₂]

  have hflip : DescentAction.flipMap (sMap R R') t ≫ (pointBC g x).1 =
      xSS ≫ DescentAction.flipMap (sMap R R') g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pointBC_coe_fst, DescentAction.flipMap_fst_assoc, Category.assoc,
        DescentAction.flipMap_fst, ← Category.assoc xSS, hxSS₁, Category.assoc, pointBC_coe_fst]
    · rw [Category.assoc, pointBC_coe_snd, DescentAction.flipMap_snd, Category.assoc, DescentAction.flipMap_snd,
        hxSS₂]
  change DescentAction.flipMap (sMap R R') t ≫ (pointBC g x).1 ≫ e.hom = yRel (pointBC' e he x) ≫ A.act
  rw [← Category.assoc, hflip, hrel, Category.assoc, Category.assoc, hact]
  rfl

theorem exists_pointBC'_eq_of_invariant [Module.FaithfullyFlat R R']
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') (hy : Invariant A y) :
    ∃ x : SchemeHomOver t g, pointBC' e he x = y := by
  have heinv : e.inv ≫ pullback.snd g (sMap R R') = g' := by rw [← he, Iso.inv_hom_id_assoc]

  let N : pullback t (sMap R R') ⟶ pullback g (sMap R R') := y.1 ≫ e.inv
  have hN₂ : N ≫ pullback.snd g (sMap R R') = pullback.snd t (sMap R R') := by
    change (y.1 ≫ e.inv) ≫ _ = _
    rw [Category.assoc, heinv, y.2]
  let NS : pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶
      pullback (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.map _ _ _ _ N (𝟙 _) (𝟙 _) (by rw [Category.comp_id, reassoc_of% hN₂])
      (by rw [Category.comp_id, Category.id_comp])
  have hNS₁ : NS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ N := pullback.lift_fst _ _ _
  have hNS₂ : NS ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hrel : yRel y = NS ≫ pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R')
      (g' ≫ sMap R R') (sMap R R') e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
      (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [yRel_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hNS₁, Category.assoc]
      change _ = pullback.fst _ _ ≫ (y.1 ≫ e.inv) ≫ e.hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [yRel_snd, Category.assoc, pullback.lift_snd, Category.comp_id, hNS₂]
  let a : pullback t (sMap R R') ⟶ B := N ≫ pullback.fst g (sMap R R')

  have hcond : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ pullback t (sMap R R')),
      g₁ ≫ pullback.fst t (sMap R R') = g₂ ≫ pullback.fst t (sMap R R') → g₁ ≫ a = g₂ ≫ a := by
    intro W g₁ g₂ hg
    have w : g₁ ≫ pullback.snd t (sMap R R') ≫ sMap R R' = (g₂ ≫ pullback.snd t (sMap R R')) ≫ sMap R R' := by
      rw [Category.assoc, ← pullback.condition, reassoc_of% hg]
    let ρ : W ⟶ pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') :=
      pullback.lift g₁ (g₂ ≫ pullback.snd t (sMap R R')) w
    have hρ₁ : g₁ = ρ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have hρ₂ : g₂ = ρ ≫ DescentAction.flipMap (sMap R R') t := by
      apply pullback.hom_ext
      · rw [Category.assoc, DescentAction.flipMap_fst, pullback.lift_fst_assoc]
        exact hg.symm
      · rw [Category.assoc, DescentAction.flipMap_snd]
        exact (pullback.lift_snd _ _ _).symm
    rw [hρ₁, hρ₂, Category.assoc, Category.assoc]
    congr 1

    change pullback.fst _ _ ≫ (y.1 ≫ e.inv) ≫ pullback.fst g (sMap R R') =
      DescentAction.flipMap (sMap R R') t ≫ (y.1 ≫ e.inv) ≫ pullback.fst g (sMap R R')
    have hy' : DescentAction.flipMap (sMap R R') t ≫ y.1 = yRel y ≫ A.act := hy
    simp only [Category.assoc]
    rw [reassoc_of% hy', hrel, Category.assoc, reassoc_of% hact]
    change _ = NS ≫ DescentAction.flipMap (sMap R R') g ≫ e.hom ≫ e.inv ≫ pullback.fst g (sMap R R')
    rw [Iso.hom_inv_id_assoc, DescentAction.flipMap_fst, reassoc_of% hNS₁]
    simp only [N, Category.assoc]
  let xl : T ⟶ B := EffectiveEpi.desc (pullback.fst t (sMap R R')) a (fun g₁ g₂ hg => hcond g₁ g₂ hg)
  have hxl : pullback.fst t (sMap R R') ≫ xl = a := EffectiveEpi.fac _ _ _
  have hxg : xl ≫ g = t := by
    apply (cancel_epi (pullback.fst t (sMap R R'))).1
    rw [← Category.assoc, hxl]
    change (N ≫ pullback.fst g (sMap R R')) ≫ g = _
    rw [Category.assoc, pullback.condition, reassoc_of% hN₂, pullback.condition]
  refine ⟨⟨xl, hxg⟩, ?_⟩
  apply Subtype.ext
  change (pointBC g ⟨xl, hxg⟩).1 ≫ e.hom = y.1
  have hlift : (pointBC g ⟨xl, hxg⟩).1 = N := by
    apply pullback.hom_ext
    · rw [pointBC_coe_fst, hxl]
    · rw [pointBC_coe_snd, hN₂]
  rw [hlift]
  change (y.1 ≫ e.inv) ≫ e.hom = y.1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pointBC'_bijective_invariant [Module.FaithfullyFlat R R']
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Bijective (fun x : SchemeHomOver t g =>
      (⟨pointBC' e he x, invariant_pointBC' A e he hact x⟩ :
        {y : SchemeHomOver (pullback.snd t (sMap R R')) g' // Invariant A y})) := by
  refine ⟨fun x₁ x₂ h => pointBC'_injective e he t (congrArg Subtype.val h), fun y => ?_⟩
  obtain ⟨x, hx⟩ := exists_pointBC'_eq_of_invariant A e he hact y.1 y.2
  exact ⟨x, Subtype.ext hx⟩

end Invariant

section GroupLaw

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g') (LB' : RelativeGroupLaw R' g')

theorem inv_natural {S₀ : Type u} [CommRing S₀] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of S₀)}
    (L : RelativeGroupLaw S₀ c) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S₀))
    (t' : T' ⟶ Spec (CommRingCat.of S₀)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t c) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]

  have h' : (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) *
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = 1 := h
  exact eq_inv_of_mul_eq_one_left h'

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

noncomputable abbrev τ₃ (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ Spec (CommRingCat.of R') :=
  pullback.snd _ _

noncomputable abbrev t'₃ (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ Spec (CommRingCat.of R') :=
  pullback.fst _ _ ≫ pullback.snd t (sMap R R')

theorem hτ₃ (t : T ⟶ Spec (CommRingCat.of R)) : t'₃ t ≫ sMap R R' = τ₃ t ≫ sMap R R' := by
  rw [Category.assoc]; exact pullback.condition

noncomputable def yfst (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : SchemeHomOver (t'₃ t) g' :=
  GoodReductionJacobian.schemeHomOverComp (pullback.fst _ _) rfl y

noncomputable def yflip (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : SchemeHomOver (τ₃ t) g' :=
  GoodReductionJacobian.schemeHomOverComp (DescentAction.flipMap (sMap R R') t) (DescentAction.flipMap_snd _ _) y

noncomputable def actP (z : SchemeHomOver (t'₃ t) g') : SchemeHomOver (τ₃ t) g' :=
  NeronModelInfra.schemeHomOverComp
    (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨z.1, by rw [reassoc_of% z.2]; exact pullback.condition⟩ :
        SchemeHomOver (τ₃ t ≫ sMap R R') (g' ≫ sMap R R')))
    (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g')

theorem actP_coe (z : SchemeHomOver (t'₃ t) g') :
    (actP A z).1 = pullback.lift z.1 (τ₃ t) (by rw [reassoc_of% z.2]; exact pullback.condition) ≫ A.act :=
  rfl

theorem invariant_iff (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    Invariant A y ↔ actP A (yfst y) = yflip y := by
  have hlift : pullback.lift (yfst y).1 (τ₃ t) (by rw [reassoc_of% (yfst y).2]; exact pullback.condition) =
      yRel y := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, yRel_fst]; rfl
    · rw [pullback.lift_snd, yRel_snd]
  constructor
  · intro h
    apply Subtype.ext
    rw [actP_coe, hlift]
    exact h.symm
  · intro h
    have h' := congrArg Subtype.val h
    rw [actP_coe, hlift] at h'
    exact h'.symm

def MulCompatible : Prop :=
  ∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (x y : SchemeHomOver t' g'),
    NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
          (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
            SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
        (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g') =
      LB'.mul τ
        (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
            (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
          (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g'))
        (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
            (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
          (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g'))

variable {A LB'}

theorem actP_mul (hA₂ : MulCompatible A LB') (x y : SchemeHomOver (t'₃ t) g') :
    actP A (LB'.mul (t'₃ t) x y) = LB'.mul (τ₃ t) (actP A x) (actP A y) :=
  hA₂ (τ₃ t) (t'₃ t) (hτ₃ t) x y

theorem actP_one (hA₂ : MulCompatible A LB') :
    actP A (LB'.one (t'₃ (R := R) (R' := R') t)) = LB'.one (τ₃ t) := by
  letI := LB'.pointGroup (τ₃ (R := R) (R' := R') t)
  have h := actP_mul (t := t) hA₂ (LB'.one _) (LB'.one _)
  rw [LB'.one_mul] at h

  have h' : actP A (LB'.one (t'₃ (R := R) (R' := R') t)) * actP A (LB'.one (t'₃ (R := R) (R' := R') t)) =
      actP A (LB'.one (t'₃ (R := R) (R' := R') t)) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

theorem actP_inv (hA₂ : MulCompatible A LB') (x : SchemeHomOver (t'₃ t) g') :
    actP A (LB'.inv (t'₃ t) x) = LB'.inv (τ₃ t) (actP A x) := by
  letI := LB'.pointGroup (τ₃ (R := R) (R' := R') t)
  have h := actP_mul (t := t) hA₂ (LB'.inv _ x) x
  rw [LB'.inv_mul_cancel, actP_one hA₂] at h
  have h' : actP A (LB'.inv (t'₃ t) x) * actP A x = 1 := h.symm
  exact eq_inv_of_mul_eq_one_left h'

theorem yfst_mul (y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yfst (LB'.mul _ y₁ y₂) = LB'.mul (t'₃ t) (yfst y₁) (yfst y₂) :=
  LB'.mul_natural _ _ _ _ _ _

theorem yflip_mul (y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yflip (LB'.mul _ y₁ y₂) = LB'.mul (τ₃ t) (yflip y₁) (yflip y₂) :=
  LB'.mul_natural _ _ _ _ _ _

theorem invariant_mul (hA₂ : MulCompatible A LB') {y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R R')) g'}
    (h₁ : Invariant A y₁) (h₂ : Invariant A y₂) : Invariant A (LB'.mul _ y₁ y₂) := by
  rw [invariant_iff] at h₁ h₂ ⊢
  rw [yfst_mul, actP_mul hA₂, h₁, h₂, yflip_mul]

theorem invariant_one (hA₂ : MulCompatible A LB') :
    Invariant A (LB'.one (pullback.snd t (sMap R R'))) := by
  rw [invariant_iff]
  change actP A (GoodReductionJacobian.schemeHomOverComp _ rfl (LB'.one _)) =
    GoodReductionJacobian.schemeHomOverComp _ _ (LB'.one _)
  rw [LB'.one_natural, LB'.one_natural, actP_one hA₂]

theorem invariant_inv (hA₂ : MulCompatible A LB') {y : SchemeHomOver (pullback.snd t (sMap R R')) g'}
    (h : Invariant A y) : Invariant A (LB'.inv _ y) := by
  rw [invariant_iff] at h ⊢
  change actP A (GoodReductionJacobian.schemeHomOverComp _ rfl (LB'.inv _ y)) =
    GoodReductionJacobian.schemeHomOverComp _ _ (LB'.inv _ y)
  rw [inv_natural, inv_natural, actP_inv hA₂]
  exact congrArg _ h

end GroupLaw

section Descended

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {A : DescentAction (sMap R R') g'} {LB' : RelativeGroupLaw R' g'}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))

variable [Module.FaithfullyFlat R R']
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₂ : MulCompatible A LB')

noncomputable def Φ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t g ≃ {y : SchemeHomOver (pullback.snd t (sMap R R')) g' // Invariant A y} :=
  Equiv.ofBijective _ (pointBC'_bijective_invariant A e he hact t)

@[scoped simp] theorem Φ_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g) :
    ((Φ (T := T) e he hact t) x).1 = pointBC' e he x := rfl

noncomputable def descendedLaw : RelativeGroupLaw R g where
  mul t x y := (Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
    invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩
  one t := (Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩
  inv t x := (Φ e he hact t).symm ⟨LB'.inv _ (pointBC' e he x), invariant_inv hA₂ ((Φ e he hact t) x).2⟩
  mul_assoc t x y z := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have hx : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
        invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩) = LB'.mul _ (pointBC' e he x) (pointBC' e he y) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    have hy : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he y) (pointBC' e he z),
        invariant_mul hA₂ ((Φ e he hact t) y).2 ((Φ e he hact t) z).2⟩) = LB'.mul _ (pointBC' e he y) (pointBC' e he z) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [hx, hy, LB'.mul_assoc]
  one_mul t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩) = LB'.one _ :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.one_mul, Φ_apply_coe]
  mul_one t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩) = LB'.one _ :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.mul_one, Φ_apply_coe]
  inv_mul_cancel t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.inv _ (pointBC' e he x), invariant_inv hA₂ ((Φ e he hact t) x).2⟩) =
        LB'.inv _ (pointBC' e he x) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (Φ e he hact t').injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, Φ_apply_coe]

    have hnat : ∀ z : SchemeHomOver t g, pointBC' e he (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
        GoodReductionJacobian.schemeHomOverComp
          (pullback.map t' (sMap R R') t (sMap R R') ψ (𝟙 _) (𝟙 _) (by rw [hψ, Category.comp_id])
            (by rw [Category.comp_id, Category.id_comp]))
          (by rw [pullback.lift_snd, Category.comp_id]) (pointBC' e he z) := by
      intro z
      apply Subtype.ext
      change (pointBC g (GoodReductionJacobian.schemeHomOverComp ψ hψ z)).1 ≫ e.hom = _
      rw [pointBC_natural]
      rfl
    have hmul : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
        invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩) = LB'.mul _ (pointBC' e he x) (pointBC' e he y) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [hnat, hmul, LB'.mul_natural, ← hnat, ← hnat]

theorem pointBC'_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g) :
    pointBC' e he ((descendedLaw e he hact hA₂).mul t x y) = LB'.mul _ (pointBC' e he x) (pointBC' e he y) :=
  congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)

theorem pointBC'_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pointBC' e he ((descendedLaw e he hact hA₂).one t) = LB'.one _ :=
  congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)

end Descended

section Embedding

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₁ : pullback.map (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act ≫ jY'.1)

include hA₁ in

theorem invariant_jY' : Invariant A jY' := hA₁.symm

theorem isPullback_pointBC (jY : SchemeHomOver (X'.ι ≫ f) g) :
    IsPullback (pointBC g jY).1 (pullback.fst (X'.ι ≫ f) (sMap R R')) (pullback.fst g (sMap R R')) jY.1 := by
  refine IsPullback.of_right ?_ (pointBC_coe_fst g jY) (IsPullback.of_hasPullback g (sMap R R')).flip
  convert (IsPullback.of_hasPullback (X'.ι ≫ f) (sMap R R')).flip using 1
  · exact pointBC_coe_snd g jY
  · exact jY.2

theorem pointBC'_comp (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t (X'.ι ≫ f)) :
    pointBC' e he (NeronModelInfra.schemeHomOverComp a jY) =
      NeronModelInfra.schemeHomOverComp (pointBC (X'.ι ≫ f) a) jY' := by
  rw [← hjY]
  apply Subtype.ext
  change (pointBC g (NeronModelInfra.schemeHomOverComp a jY)).1 ≫ e.hom =
    (pointBC (X'.ι ≫ f) a).1 ≫ (pointBC g jY).1 ≫ e.hom
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [pointBC_coe_fst, Category.assoc, pointBC_coe_fst, ← Category.assoc, pointBC_coe_fst, Category.assoc]
    rfl
  · rw [pointBC_coe_snd, Category.assoc, pointBC_coe_snd, pointBC_coe_snd]

variable [Module.FaithfullyFlat R R']

include hact hA₁ in

theorem exists_jY : ∃ jY : SchemeHomOver (X'.ι ≫ f) g, pointBC' e he jY = jY' :=
  exists_pointBC'_eq_of_invariant A e he hact jY' (invariant_jY' A f X' jY' hA₁)

theorem isOpenImmersion_jY [IsOpenImmersion jY'.1] (jY : SchemeHomOver (X'.ι ≫ f) g)
    (hjY : pointBC' e he jY = jY') : IsOpenImmersion jY.1 := by
  have h1 : IsOpenImmersion ((pointBC g jY).1 ≫ e.hom) := by
    have : (pointBC' e he jY).1 = jY'.1 := by rw [hjY]
    rw [pointBC'_coe] at this
    rw [this]; infer_instance
  have h2 : IsOpenImmersion (pointBC g jY).1 :=
    (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ e.hom).mp h1
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (pullback.fst g (sMap R R')) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_pointBC f X' jY) hQ h2

end Embedding

section Restrict

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {A : DescentAction (sMap R R') g'} {LB' : RelativeGroupLaw R' g'}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
      (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
      (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
    a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
    c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
    NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
      LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') a) jY')
        (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b) jY'))

variable [Module.FaithfullyFlat R R']
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₂ : MulCompatible A LB')

omit [Module.FaithfullyFlat R R'] in

theorem pointBC_eq_baseChangePointOfBase {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t y) :
    pointBC y a = RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨pullback.fst t (sMap R R') ≫ a.1, by rw [Category.assoc, a.2, pullback.condition]⟩ :
        SchemeHomOver (pullback.snd t (sMap R R') ≫ sMap R R') y) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [pointBC_coe_fst, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  · rw [pointBC_coe_snd, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]

include hres' in

theorem descended_restricts (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f))
    (ha : a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f) (hb : b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f)
    (hc : c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) :
    NeronModelInfra.schemeHomOverComp c jY =
      (descendedLaw e he hact hA₂).mul t (NeronModelInfra.schemeHomOverComp a jY)
        (NeronModelInfra.schemeHomOverComp b jY) := by
  apply pointBC'_injective e he t
  rw [pointBC'_mul, pointBC'_comp e he f X' jY' jY hjY, pointBC'_comp e he f X' jY' jY hjY,
    pointBC'_comp e he f X' jY' jY hjY, pointBC_eq_baseChangePointOfBase, pointBC_eq_baseChangePointOfBase,
    pointBC_eq_baseChangePointOfBase]
  let π := pullback.fst t (sMap R R')
  refine hres' (pullback.snd t (sMap R R'))
    ⟨π ≫ w.1, by rw [Category.assoc, w.2, pullback.condition]⟩ _ _ _ ?_ ?_ ?_
  · change (π ≫ a.1) ≫ X'.ι = (π ≫ w.1) ≫ U.ι ≫ pullback.fst f f
    rw [Category.assoc, ha, Category.assoc]
  · change (π ≫ b.1) ≫ X'.ι = (π ≫ w.1) ≫ U.ι ≫ pullback.snd f f
    rw [Category.assoc, hb, Category.assoc]
  · change (π ≫ c.1) ≫ X'.ι = (π ≫ w.1) ≫ (pullback f f).homOfLE hUW ≫ m.1
    rw [Category.assoc, hc, Category.assoc]

end Restrict

theorem exists_maximal_specializes {Y : Type u} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    {F : Set Y} (hF : IsClosed F) {b : Y} (hb : b ∈ F) :
    ∃ η ∈ F, η ⤳ b ∧ ∀ y ∈ F, y ⤳ η → y = η := by
  let b₀ : F := ⟨b, hb⟩
  let C : Set F := irreducibleComponent b₀
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_irreducibleComponent
  let C' : Set Y := Subtype.val '' C
  have hC' : IsIrreducible C' := hC.image _ continuous_subtype_val.continuousOn
  have hC'cl : IsClosed C' := hF.isClosedEmbedding_subtypeVal.isClosedMap _ hCcl
  have hgen : IsGenericPoint hC'.genericPoint C' := hC'.isGenericPoint_genericPoint hC'cl
  set η := hC'.genericPoint with hη
  have hηC' : η ∈ C' := hgen.mem
  have hC'F : C' ⊆ F := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  refine ⟨η, hC'F hηC', hgen.specializes ⟨b₀, mem_irreducibleComponent, rfl⟩, ?_⟩
  intro y hy hyη
  let y₀ : F := ⟨y, hy⟩

  have hS : IsIrreducible (closure ({y₀} : Set F)) := isIrreducible_singleton.closure
  have hCS : C ⊆ closure ({y₀} : Set F) := by
    intro z hz
    have hz' : (z : Y) ∈ C' := ⟨z, hz, rfl⟩
    have h1 : y ⤳ (z : Y) := hyη.trans (hgen.specializes hz')
    have h2 : y₀ ⤳ z := (subtype_specializes_iff y₀ z).2 h1
    exact h2.mem_closed isClosed_closure (subset_closure (Set.mem_singleton y₀))
  have hSC : closure ({y₀} : Set F) = C := eq_irreducibleComponent hS.2 hCS
  have hyC : y₀ ∈ C := by
    rw [← hSC]
    exact subset_closure (Set.mem_singleton y₀)
  have hyC' : y ∈ C' := ⟨y₀, hyC, rfl⟩
  have hηy : η ⤳ y := hgen.specializes hyC'
  exact (hyη.antisymm hηy).eq

section ClosedPoint

variable (R R')
variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']

theorem sMap_base_eq_closedPoint_iff (p : ↥(Spec (CommRingCat.of R'))) :
    (sMap R R').base p = IsLocalRing.closedPoint R ↔ p = IsLocalRing.closedPoint R' := by
  have hcomap : ∀ q : PrimeSpectrum R', ((sMap R R').base q).asIdeal = q.asIdeal.comap (algebraMap R R') :=
    fun q => rfl
  constructor
  · intro h
    have h1 : (p.asIdeal.comap (algebraMap R R')).IsMaximal := by
      rw [← hcomap, h]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have h2 : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal h2
  · intro h
    subst h
    apply PrimeSpectrum.ext
    rw [hcomap]
    haveI : (IsLocalRing.closedPoint R').asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R'
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)

end ClosedPoint

section Density

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')

include hjY in

theorem fst_mem_range_of_mem_range {b₁ : ↥(pullback g (sMap R R'))}
    (h : e.hom.base b₁ ∈ Set.range jY'.1.base) : (pullback.fst g (sMap R R')).base b₁ ∈ Set.range jY.1.base := by
  obtain ⟨y, hy⟩ := h
  have hval : jY'.1 = (pointBC g jY).1 ≫ e.hom := by rw [← hjY]; rfl
  rw [hval, Scheme.Hom.comp_apply] at hy
  have hinj : Function.Injective e.hom.base := e.hom.homeomorph.injective
  have hy' : (pointBC g jY).1.base y = b₁ := hinj hy
  refine ⟨(pullback.fst (X'.ι ≫ f) (sMap R R')).base y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pointBC_coe_fst g jY, Scheme.Hom.comp_apply, hy']

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']

omit [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [Module.FaithfullyFlat R R'] in
include he in
theorem g_fst_eq (b₁ : ↥(pullback g (sMap R R'))) :
    g.base ((pullback.fst g (sMap R R')).base b₁) = (sMap R R').base (g'.base (e.hom.base b₁)) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.hom g', he]

include he hjY in

theorem mem_range_jY_of_ne (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (b : B) (hb : g.base b ≠ IsLocalRing.closedPoint R) : b ∈ Set.range jY.1.base := by
  obtain ⟨b₁, rfl⟩ := (inferInstance : Surjective (pullback.fst g (sMap R R'))).surj b
  apply fst_mem_range_of_mem_range e he f X' jY' jY hjY
  apply hjY'₁
  intro hc
  apply hb
  rw [g_fst_eq e he, hc]
  exact (sMap_base_eq_closedPoint_iff R R' _).2 rfl

include he hjY in

theorem mem_range_jY_of_maximal
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (b : B) (hb : g.base b = IsLocalRing.closedPoint R)
    (hmax : ∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) : b ∈ Set.range jY.1.base := by
  obtain ⟨b₁, rfl⟩ := (inferInstance : Surjective (pullback.fst g (sMap R R'))).surj b

  let F : Set ↥B' := g'.base ⁻¹' {IsLocalRing.closedPoint R'}
  have hF : IsClosed F := (IsLocalRing.isClosed_singleton_closedPoint R').preimage g'.base.hom.continuous
  have hb' : e.hom.base b₁ ∈ F := by
    change g'.base (e.hom.base b₁) = IsLocalRing.closedPoint R'
    rw [← sMap_base_eq_closedPoint_iff R R', ← g_fst_eq e he]
    exact hb
  obtain ⟨η, hηF, hηb, hηmax⟩ := exists_maximal_specializes hF hb'
  have hη : η ∈ Set.range jY'.1.base := hjY'₂ η hηF (fun y hy hyF => hηmax y hyF hy)

  let η₁ : ↥(pullback g (sMap R R')) := e.inv.base η
  have hη₁ : e.hom.base η₁ = η := by
    change (e.inv ≫ e.hom).base η = η
    rw [Iso.inv_hom_id]; rfl
  have hspec : (pullback.fst g (sMap R R')).base η₁ ⤳ (pullback.fst g (sMap R R')).base b₁ := by
    have h1 : η₁ ⤳ e.inv.base (e.hom.base b₁) := hηb.map e.inv.base.hom.continuous
    have h2 : e.inv.base (e.hom.base b₁) = b₁ := by
      change (e.hom ≫ e.inv).base b₁ = b₁
      rw [Iso.hom_inv_id]; rfl
    rw [h2] at h1
    exact h1.map (pullback.fst g (sMap R R')).base.hom.continuous
  have hclosed : g.base ((pullback.fst g (sMap R R')).base η₁) = IsLocalRing.closedPoint R := by
    rw [g_fst_eq e he, hη₁, sMap_base_eq_closedPoint_iff R R']
    exact hηF
  have heq : (pullback.fst g (sMap R R')).base η₁ = (pullback.fst g (sMap R R')).base b₁ := hmax _ hspec hclosed
  rw [← heq]
  apply fst_mem_range_of_mem_range e he f X' jY' jY hjY
  rw [hη₁]
  exact hη

end Density

section GenericFibre

variable {S₀ : Scheme.{u}} (ι : S₀ ⟶ Spec (CommRingCat.of R))
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)

theorem isPullback_map (jY : SchemeHomOver (X'.ι ≫ f) g) :
    IsPullback
      (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp]))
      (pullback.fst (X'.ι ≫ f) ι) (pullback.fst g ι) jY.1 := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback g ι).flip
  convert (IsPullback.of_hasPullback (X'.ι ≫ f) ι).flip using 1
  · exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  · exact jY.2

theorem isIso_map_of_forall_mem_range (jY : SchemeHomOver (X'.ι ≫ f) g) [IsOpenImmersion jY.1]
    (hdense : ∀ b : B, g.base b ∈ Set.range ι.base → b ∈ Set.range jY.1.base) :
    IsIso (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])) := by
  have hP := isPullback_map ι f X' jY
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip inferInstance, ⟨fun q => ?_⟩⟩

  have hq : (pullback.fst g ι).base q ∈ Set.range jY.1.base := by
    apply hdense
    refine ⟨(pullback.snd g ι).base q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]

  have hrange : Set.range (hP.isoPullback.hom ≫ pullback.fst (pullback.fst g ι) jY.1).base =
      Set.range (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])).base := by
    rw [hP.isoPullback_hom_fst]
  have hq' : q ∈ Set.range (pullback.fst (pullback.fst g ι) jY.1).base := by
    rw [Scheme.Pullback.range_fst]
    exact hq
  obtain ⟨z, hz⟩ := hq'
  refine ⟨hP.isoPullback.inv.base z, ?_⟩
  have : (hP.isoPullback.inv ≫ pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])) = pullback.fst (pullback.fst g ι) jY.1 := by
    rw [Iso.inv_comp_eq, hP.isoPullback_hom_fst]
  rw [← Scheme.Hom.comp_apply, this]
  exact hz

end GenericFibre

section GenericIso

variable [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem specGenericFibreInclusion_ne_closedPoint (p : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : ((specGenericFibreInclusion R K).base p).asIdeal = ⊥ := by
    change (p.asIdeal.comap (algebraMap R K)) = ⊥
    have hp : p.asIdeal = ⊥ := by
      haveI := p.isPrime
      exact (Ideal.eq_bot_of_prime p.asIdeal)
    rw [hp]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
  rw [h] at h1
  exact IsDiscreteValuationRing.not_a_field R h1

variable {K}
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
  (X' : X.Opens) (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (jY : SchemeHomOver (X'.ι ≫ f) g)
  (hjY₁ : ∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base)

include hjY₁ in

theorem isIso_genericFibreRestrict_jY [IsOpenImmersion jY.1] : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap g (X'.ι ≫ f) jY (by rw [jY.2, Category.comp_id])
    (by rw [Category.comp_id, Category.id_comp])]
  apply isIso_map_of_forall_mem_range
  rintro b ⟨p, hp⟩
  apply hjY₁
  rw [← hp]
  exact specGenericFibreInclusion_ne_closedPoint K p

include hX'₁ in

theorem isIso_genericFibreRestrict_incl :
    IsIso (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap f (X'.ι ≫ f) ⟨X'.ι, rfl⟩ (Category.comp_id _)
    (by rw [Category.comp_id, Category.id_comp])]
  haveI : IsOpenImmersion (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f).1 := by
    change IsOpenImmersion X'.ι; infer_instance
  apply isIso_map_of_forall_mem_range
  rintro b ⟨p, hp⟩
  have hb : b ∈ X' := hX'₁ b (by rw [← hp]; exact specGenericFibreInclusion_ne_closedPoint K p)
  change b ∈ Set.range X'.ι.base
  rw [Scheme.Opens.range_ι]
  exact hb

noncomputable def ePrime (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK :=
  ⟨inv (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 ≫ (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 ≫ e.1,
    by
      rw [Category.assoc, Category.assoc, e.2, (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).2,
        IsIso.inv_comp_eq, (genericFibreRestrict R K g (X'.ι ≫ f) jY).2]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem ePrime_coe (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    (ePrime f e X' jY hiso).1 = inv (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 ≫
      (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 ≫ e.1 :=
  rfl

include hX'₁ in
theorem isIso_ePrime [IsIso e.1] (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    IsIso (ePrime f e X' jY hiso).1 := by
  haveI := isIso_genericFibreRestrict_incl (K := K) f X' hX'₁
  rw [ePrime_coe]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem ePrime_compat (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) (ePrime f e X' jY hiso) =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ePrime_coe,
    IsIso.hom_inv_id_assoc]

end GenericIso

section Hhom

variable [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem bcOfBase_comp {A₁ B₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {g₁ : B₁ ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver g₁ f₁) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (y : SchemeHomOver (t ≫ specGenericFibreInclusion R K) g₁) :
    RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp y φ) =
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y)
        (genericFibreRestrict R K f₁ g₁ φ) := by
  rw [← RelativeGroupLaw.baseChangePointOfBase_toBase (specGenericFibreInclusion R K)
      (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y)
        (genericFibreRestrict R K f₁ g₁ φ)),
    RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict, RelativeGroupLaw.baseChangePointToBase_ofBase]

variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
  (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (hmK : (NeronModelInfra.schemeHomOverComp
      (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
    pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
        (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst f f ≫ f)
            ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
  (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
  (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
  (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
    m.1.base ⟨q, hUW hq⟩ ∈ X')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
  (jY : SchemeHomOver (X'.ι ≫ f) g)
  (hres : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
    a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
    c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
    NeronModelInfra.schemeHomOverComp c jY =
      LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY))
  (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1)

include hmK hU₁ hU₂ hres in

theorem ePrime_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) (ePrime f e X' jY hiso) =
      LXK.mul t (NeronModelInfra.schemeHomOverComp x (ePrime f e X' jY hiso))
        (NeronModelInfra.schemeHomOverComp y (ePrime f e X' jY hiso)) := by

  set jYK := genericFibreRestrict R K g (X'.ι ≫ f) jY with hjYK
  set iXK := genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩ with hiXK
  set e' := ePrime f e X' jY hiso with he'
  haveI : IsIso jYK.1 := hiso
  have hcompat : NeronModelInfra.schemeHomOverComp jYK e' = NeronModelInfra.schemeHomOverComp iXK e :=
    ePrime_compat f e X' jY hiso

  let invJ : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) (pullback.snd (X'.ι ≫ f) (specGenericFibreInclusion R K)) :=
    ⟨inv jYK.1, by rw [IsIso.inv_comp_eq, jYK.2]⟩
  have hinvJ : ∀ z : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K)),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z invJ) jYK = z := by
    intro z
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, IsIso.inv_hom_id, Category.comp_id, invJ]
  let αK := NeronModelInfra.schemeHomOverComp x invJ
  let βK := NeronModelInfra.schemeHomOverComp y invJ
  let α : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) := RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) αK
  let β : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) := RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) βK
  have hE1x : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) x = NeronModelInfra.schemeHomOverComp α jY := by
    rw [← hinvJ x]
    exact RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K jY αK
  have hE1y : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) y = NeronModelInfra.schemeHomOverComp β jY := by
    rw [← hinvJ y]
    exact RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K jY βK

  have hαf : (α.1 ≫ X'.ι) ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw [Category.assoc]; exact α.2
  have hβf : (β.1 ≫ X'.ι) ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw [Category.assoc]; exact β.2
  let pair : T ⟶ pullback f f := pullback.lift (α.1 ≫ X'.ι) (β.1 ≫ X'.ι) (hαf.trans hβf.symm)
  have hpair : pair ≫ pullback.fst f f ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw [pullback.lift_fst_assoc, hαf]
  have hrange : Set.range pair.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hU₁
    intro hc
    have h1 : (pullback.fst f f ≫ f).base (pair.base z) = (specGenericFibreInclusion R K).base (t.base z) := by
      rw [← Scheme.Hom.comp_apply, hpair, Scheme.Hom.comp_apply]
    rw [h1] at hc
    exact specGenericFibreInclusion_ne_closedPoint K _ hc
  let wl : T ⟶ U := IsOpenImmersion.lift U.ι pair hrange
  have hwl : wl ≫ U.ι = pair := IsOpenImmersion.lift_fac _ _ _
  let w : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (U.ι ≫ pullback.fst f f ≫ f) := ⟨wl, by rw [reassoc_of% hwl, hpair]⟩
  have ha : α.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_fst]
  have hb : β.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_snd]

  let cm : T ⟶ X := w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1
  have hrangec : Set.range cm.base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : (U.ι.base (wl.base z)) ∈ U := by
      rw [Scheme.Opens.ι_apply]; exact (wl.base z).2
    have h3 := (hU₂ _ hq).2.2
    have hpt : ((pullback f f).homOfLE hUW).base (wl.base z) = ⟨U.ι.base (wl.base z), hUW hq⟩ := by
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
      rfl
    change m.1.base (((pullback f f).homOfLE hUW).base (wl.base z)) ∈ X'
    rw [hpt]
    exact h3
  let cl : T ⟶ X' := IsOpenImmersion.lift X'.ι cm hrangec
  have hcl : cl ≫ X'.ι = cm := IsOpenImmersion.lift_fac _ _ _
  have hwW : (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t ≫ (specGenericFibreInclusion R K) := by
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]
    exact w.2
  let c : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) := ⟨cl, by
    rw [reassoc_of% hcl]
    change (w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) ≫ f = t ≫ (specGenericFibreInclusion R K)
    rw [Category.assoc, Category.assoc, m.2, ← Category.assoc]
    exact hwW⟩
  have hc : c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 := hcl

  have hE3 : NeronModelInfra.schemeHomOverComp c jY =
      LB.mul (t ≫ (specGenericFibreInclusion R K)) (NeronModelInfra.schemeHomOverComp α jY) (NeronModelInfra.schemeHomOverComp β jY) :=
    hres (t ≫ (specGenericFibreInclusion R K)) w α β c ha hb hc

  have hE4 : (LB.genericFibre K).mul t x y =
      RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp c jY) := by
    rw [RelativeGroupLaw.baseChange_mul, hE1x, hE1y, ← hE3]

  let wW : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (W.ι ≫ pullback.fst f f ≫ f) := ⟨w.1 ≫ (pullback f f).homOfLE hUW, hwW⟩
  have hcm : NeronModelInfra.schemeHomOverComp c (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp wW m := by
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hc, Category.assoc]

  have hL : NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) wW)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e) := by
    rw [hE4, bcOfBase_comp, NeronModelInfra.schemeHomOverComp_assoc, ← hjYK, hcompat, hiXK,
      ← NeronModelInfra.schemeHomOverComp_assoc, ← bcOfBase_comp, hcm, bcOfBase_comp,
      NeronModelInfra.schemeHomOverComp_assoc]

  set wK := RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) wW with hwK
  let s₀ := pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let prW : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f) := ⟨W.ι, rfl⟩
  let pK : SchemeHomOver t s₀ := NeronModelInfra.schemeHomOverComp wK (genericFibreRestrict R K _ _ prW)
  have hprW : (genericFibreRestrict R K (pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) prW).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
        (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) :=
    genericFibreRestrict_coe_eq_pullbackMap _ _ prW _ _

  let P := NeronModelInfra.schemeHomOverComp
    (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e
  let Q := NeronModelInfra.schemeHomOverComp
    (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩) e
  have hL2 : NeronModelInfra.schemeHomOverComp wK
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e) =
      LXK.mul t (GoodReductionJacobian.schemeHomOverComp pK.1 pK.2 P)
        (GoodReductionJacobian.schemeHomOverComp pK.1 pK.2 Q) := by
    rw [← LXK.mul_natural]
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, hmK, GoodReductionJacobian.schemeHomOverComp_coe,
      NeronModelInfra.schemeHomOverComp_coe, hprW, Category.assoc]
  rw [hL, hL2]

  have hPQ : ∀ (pr : SchemeHomOver (pullback.fst f f ≫ f) f) (γ : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f))
      (γK : SchemeHomOver t (pullback.snd (X'.ι ≫ f) (specGenericFibreInclusion R K)))
      (hγK : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) γK = γ)
      (hγ : γ.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pr.1),
      GoodReductionJacobian.schemeHomOverComp pK.1 pK.2
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr) e) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp γK jYK) e' := by
    intro pr γ γK hγK hγ
    have h1 : GoodReductionJacobian.schemeHomOverComp pK.1 pK.2
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr) e) =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp pK (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr)) e := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc]
    have h2 : NeronModelInfra.schemeHomOverComp pK (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr) =
        NeronModelInfra.schemeHomOverComp γK iXK := by
      change NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp wK
        (genericFibreRestrict R K _ _ prW)) _ = _
      rw [hwK, ← bcOfBase_comp, ← bcOfBase_comp, hiXK, ← RelativeGroupLaw.baseChangePointOfBase_toBase (specGenericFibreInclusion R K) γK,
        hγK, ← bcOfBase_comp]
      congr 1
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
      change (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pr.1 = γ.1 ≫ X'.ι
      rw [hγ, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [h1, h2, NeronModelInfra.schemeHomOverComp_assoc, ← hcompat, ← NeronModelInfra.schemeHomOverComp_assoc]
  rw [hPQ ⟨pullback.fst f f, rfl⟩ α αK rfl ha, hPQ ⟨pullback.snd f f, pullback.condition.symm⟩ β βK rfl hb,
    hinvJ x, hinvJ y]

end Hhom

end R4W3GDEngine
p2m_reactivate "P2MW.S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion.R4W3GDEngine"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b) jY'))
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g')
    (hA₁ :
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫ jY'.1)
    (hA₂ : ∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g')))
    (hA : A.Effective) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY)) := by

  obtain ⟨B, g, eB, heB, hact⟩ := hA
  have hA₂' : R4W3GDEngine.MulCompatible A LB' := fun τ t' hτ x y => hA₂ τ t' hτ x y

  let LB : RelativeGroupLaw R g := R4W3GDEngine.descendedLaw eB heB hact hA₂'
  obtain ⟨jY, hjY⟩ := R4W3GDEngine.exists_jY A eB heB f X' jY' hact hA₁
  have hprops := R4W3GDEngine.props_descend R R' g g' eB heB
  have hopen : IsOpenImmersion jY.1 := R4W3GDEngine.isOpenImmersion_jY eB heB f X' jY' jY hjY
  have hres : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp c jY =
        LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY) :=
    fun t w a b c ha hb hc =>
      R4W3GDEngine.descended_restricts eB heB f W m X' U hUW jY' hres' hact hA₂' jY hjY t w a b c ha hb hc
  have hd₁ : ∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base :=
    R4W3GDEngine.mem_range_jY_of_ne eB heB f X' jY' jY hjY hjY'₁
  have hd₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base :=
    R4W3GDEngine.mem_range_jY_of_maximal eB heB f X' jY' jY hjY hjY'₂

  have hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 :=
    R4W3GDEngine.isIso_genericFibreRestrict_jY f X' jY hd₁
  refine ⟨B, g, LB, jY, R4W3GDEngine.ePrime f e X' jY hiso, hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2,
    hopen, hd₁, hd₂, R4W3GDEngine.isIso_ePrime f e X' hX'₁ jY hiso, ?_, R4W3GDEngine.ePrime_compat f e X' jY hiso,
    hres⟩
  intro T t x y
  exact R4W3GDEngine.ePrime_hom LXK f e W m hmK X' U hUW hU₁ hU₂ LB jY hres hiso t x y

end S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion
end P2MW
export P2MW.S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion (solution)
