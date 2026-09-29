-- Prove2me | solution 1 for NeronModelInfra.exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/17cbaf3a-6833-53a0-818d-f94af62e62dd

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mGlueTranslate534

section General

theorem exists_lift_of_isClosedImmersion {D G Z : Scheme.{u}} [IsReduced D] (f : D ⟶ Z) (γ : G ⟶ Z)
    [IsClosedImmersion γ] (h : Set.range f.base ⊆ Set.range γ.base) : ∃ g : D ⟶ G, g ≫ γ = f := by
  haveI : Surjective (pullback.fst f γ) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro d
    exact h ⟨d, rfl⟩⟩
  haveI : IsIso (pullback.fst f γ) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f γ) ≫ pullback.snd f γ, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem mem_of_dense_of_forall_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [TopologicalSpace.NoetherianSpace X] {W : Set X} (hWo : IsOpen W) (hWd : Dense W) (x : X)
    (hx : ∀ x' : X, x' ⤳ x → x' = x) : x ∈ W := by

  set C := irreducibleComponent x with hC
  have hCmem : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hCirr : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_irreducibleComponent
  obtain ⟨η, hη⟩ := QuasiSober.sober hCirr hCcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]
    exact mem_irreducibleComponent
  have hηeq : η = x := hx η hηx

  obtain ⟨o, ho, hone, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hCmem
  obtain ⟨z, hzo, hzW⟩ := hWd.inter_open_nonempty o ho hone
  have hz : η ⤳ z := by
    rw [specializes_iff_mem_closure, hη.def]
    exact hoC hzo
  rw [← hηeq]
  exact hz.mem_open hWo hzW

variable {A B C : Scheme.{u}} (f : A ⟶ B) (g : A ⟶ C) [IsOpenImmersion f] [IsOpenImmersion g]

theorem isOpenImmersion_inl : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) .left))

theorem isOpenImmersion_inr : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) .right))

theorem inl_eq_inr_iff (b : B) (c : C) :
    (pushout.inl f g).base b = (pushout.inr f g).base c ↔ ∃ x : A, f.base x = b ∧ g.base x = c := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g) (i := .left) (j := .right) (xi := b)
    (xj := c)).trans ?_
  constructor
  · rintro ⟨k, fi, fj, x, h1, h2⟩
    obtain - | k := fi
    · obtain - | - := fj
    · obtain - | - := fj
      exact ⟨x, h1, h2⟩
  · rintro ⟨x, h1, h2⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, x, h1, h2⟩

theorem inl_or_inr (p : ↑(pushout f g)) :
    p ∈ Set.range (pushout.inl f g).base ∨ p ∈ Set.range (pushout.inr f g).base := by
  obtain ⟨i, xi, h⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) p
  obtain - | i := i
  · left
    refine ⟨f.base xi, ?_⟩
    rw [← h]
    change (colimit.ι (span f g) WalkingSpan.left).base (((span f g).map WalkingSpan.Hom.fst).base xi) = _
    rw [← Scheme.Hom.comp_apply, colimit.w]
  · cases i with
    | left => exact Or.inl ⟨xi, h⟩
    | right => exact Or.inr ⟨xi, h⟩

theorem isPullback_inl_inr : IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  haveI := isOpenImmersion_inl f g
  haveI := isOpenImmersion_inr f g
  have hrange : Set.range (pullback.snd (pushout.inl f g) (pushout.inr f g)).base = Set.range g.base := by
    rw [Scheme.Pullback.range_snd]
    ext c
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨x, -, hx⟩ := (inl_eq_inr_iff f g b c).mp hb
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f.base x, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]⟩
  let e : A ≅ pullback (pushout.inl f g) (pushout.inr f g) :=
    (IsOpenImmersion.isoOfRangeEq g (pullback.snd (pushout.inl f g) (pushout.inr f g)) hrange.symm)
  have he : e.hom ≫ pullback.snd _ _ = g := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine IsPullback.of_iso_pullback ⟨pushout.condition⟩ e ?_ he
  rw [← cancel_mono (pushout.inl f g), Category.assoc, pullback.condition, ← Category.assoc, he,
    pushout.condition]

end General

section Data

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

abbrev Y3 : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

abbrev p12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) y

abbrev p13 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y)
    (pullback.snd (pullback.fst y y ≫ y) y) (by rw [Category.assoc]; exact pullback.condition)

abbrev p23 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y)
    (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

abbrev jA : Y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (y ≫ a) (𝟙 Y) (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

abbrev sA : pullback y y ⟶ Y3 y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y)
    (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
      (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
    (pullback.snd y y)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id, pullback.condition])

abbrev Ga : Scheme.{u} := pullback γ (sA y a ha)

abbrev cA : Ga y γ a ha ⟶ pullback y y := pullback.snd γ (sA y a ha)

def pτ : Ga y γ a ha ⟶ Y := cA y γ a ha ≫ pullback.fst y y

def pι : Ga y γ a ha ⟶ Y := cA y γ a ha ≫ pullback.snd y y

theorem pτ_def : pτ y γ a ha = cA y γ a ha ≫ pullback.fst y y := rfl

theorem pι_def : pι y γ a ha = cA y γ a ha ≫ pullback.snd y y := rfl

theorem sA_p12 : sA y a ha ≫ p12 y = pullback.fst y y ≫ jA y a ha := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

theorem sA_p13 : sA y a ha ≫ p13 y = pullback.snd y y ≫ jA y a ha := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc,
      pullback.lift_fst, ← Category.assoc, pullback.condition, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.comp_id]

theorem sA_p23 : sA y a ha ≫ p23 y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

theorem isPullback_sA_fst : IsPullback (sA y a ha) (pullback.fst y y) (p12 y) (jA y a ha) := by
  have comm : sA y a ha ≫ p12 y = pullback.fst y y ≫ jA y a ha := sA_p12 y a ha
  have c1 : pullback.fst (p12 y) (jA y a ha) ≫ p12 y ≫ pullback.fst y y =
      pullback.snd (p12 y) (jA y a ha) ≫ y ≫ a := by
    rw [← Category.assoc, pullback.condition, Category.assoc, pullback.lift_fst]
  have c2 : pullback.fst (p12 y) (jA y a ha) ≫ p12 y ≫ pullback.snd y y =
      pullback.snd (p12 y) (jA y a ha) := by
    rw [← Category.assoc, pullback.condition, Category.assoc, pullback.lift_snd, Category.comp_id]
  have key : pullback.fst (p12 y) (jA y a ha) ≫ p23 y ≫ sA y a ha = pullback.fst (p12 y) (jA y a ha) := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [reassoc_of% c2, c1]
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd]
  let e : pullback y y ≅ pullback (p12 y) (jA y a ha) :=
    { hom := pullback.lift (sA y a ha) (pullback.fst y y) comm
      inv := pullback.fst (p12 y) (jA y a ha) ≫ p23 y
      hom_inv_id := by rw [pullback.lift_fst_assoc, sA_p23]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, key, Category.id_comp]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.id_comp, pullback.lift_fst]
          exact c2 }
  exact IsPullback.of_iso_pullback ⟨comm⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem isPullback_sA_snd : IsPullback (sA y a ha) (pullback.snd y y) (p13 y) (jA y a ha) := by
  have comm : sA y a ha ≫ p13 y = pullback.snd y y ≫ jA y a ha := sA_p13 y a ha
  have c1 : pullback.fst (p13 y) (jA y a ha) ≫ p12 y ≫ pullback.fst y y =
      pullback.snd (p13 y) (jA y a ha) ≫ y ≫ a := by
    have := pullback.condition (f := p13 y) (g := jA y a ha)
    have h2 := congrArg (· ≫ pullback.fst y y) this
    simp only [Category.assoc, pullback.lift_fst] at h2
    exact h2
  have c2 : pullback.fst (p13 y) (jA y a ha) ≫ pullback.snd (pullback.fst y y ≫ y) y =
      pullback.snd (p13 y) (jA y a ha) := by
    have := pullback.condition (f := p13 y) (g := jA y a ha)
    have h2 := congrArg (· ≫ pullback.snd y y) this
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at h2
    exact h2

  have key : pullback.fst (p13 y) (jA y a ha) ≫ p23 y ≫ sA y a ha = pullback.fst (p13 y) (jA y a ha) := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]

        rw [← Category.assoc (pullback.snd y y) y a, ← pullback.condition (f := y) (g := y),
          pullback.condition_assoc, reassoc_of% c2]
        exact c1.symm
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd]
  let e : pullback y y ≅ pullback (p13 y) (jA y a ha) :=
    { hom := pullback.lift (sA y a ha) (pullback.snd y y) comm
      inv := pullback.fst (p13 y) (jA y a ha) ≫ p23 y
      hom_inv_id := by rw [pullback.lift_fst_assoc, sA_p23]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, key, Category.id_comp]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.id_comp, pullback.lift_snd]
          exact c2 }
  exact IsPullback.of_iso_pullback ⟨comm⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem isOpenImmersion_pτ [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)] : IsOpenImmersion (pτ y γ a ha) := by
  have h := (IsPullback.of_hasPullback γ (sA y a ha)).paste_vert (isPullback_sA_fst y a ha)
  rw [pτ_def, show cA y γ a ha ≫ pullback.fst y y = h.isoPullback.hom ≫ pullback.snd _ _ from
    (h.isoPullback_hom_snd).symm]
  infer_instance

theorem isOpenImmersion_pι [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc]; exact pullback.condition))] : IsOpenImmersion (pι y γ a ha) := by
  have h := (IsPullback.of_hasPullback γ (sA y a ha)).paste_vert (isPullback_sA_snd y a ha)
  rw [pι_def, show cA y γ a ha ≫ pullback.snd y y = h.isoPullback.hom ≫ pullback.snd _ _ from
    (h.isoPullback_hom_snd).symm]
  infer_instance

end Data

section Glue

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
variable [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]

omit [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)] in
theorem pτ_y : pτ y γ a ha ≫ y = pι y γ a ha ≫ y := by
  simp only [pτ_def, pι_def, Category.assoc, pullback.condition]

abbrev Yg : Scheme.{u} := pushout (pτ y γ a ha) (pι y γ a ha)

abbrev yg : Yg y γ a ha ⟶ Spec (CommRingCat.of R) := pushout.desc y y (pτ_y y γ a ha)

abbrev τg : Y ⟶ Yg y γ a ha := pushout.inl (pτ y γ a ha) (pι y γ a ha)

abbrev ιg : Y ⟶ Yg y γ a ha := pushout.inr (pτ y γ a ha) (pι y γ a ha)

theorem τg_yg : τg y γ a ha ≫ yg y γ a ha = y := pushout.inl_desc _ _ (pτ_y y γ a ha)

theorem ιg_yg : ιg y γ a ha ≫ yg y γ a ha = y := pushout.inr_desc _ _ (pτ_y y γ a ha)

scoped instance : IsOpenImmersion (τg y γ a ha) := isOpenImmersion_inl _ _

scoped instance : IsOpenImmersion (ιg y γ a ha) := isOpenImmersion_inr _ _

theorem isPullback_τg_ιg : IsPullback (pτ y γ a ha) (pι y γ a ha) (τg y γ a ha) (ιg y γ a ha) :=
  isPullback_inl_inr _ _

theorem cover (p : ↑(Yg y γ a ha)) :
    p ∈ Set.range (ιg y γ a ha).base ∨ p ∈ Set.range (τg y γ a ha).base :=
  (inl_or_inr (pτ y γ a ha) (pι y γ a ha) p).symm

theorem of_openCover_yg (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h0 : P (pτ y γ a ha ≫ y)) (h1 : P y) : P (yg y γ a ha) := by
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (span (pτ y γ a ha) (pι y γ a ha)))
  intro i
  obtain - | i := i
  · simp only [Scheme.IsLocallyDirected.openCover_f]
    rw [← colimit.w (span (pτ y γ a ha) (pι y γ a ha)) WalkingSpan.Hom.fst]
    change P ((pτ y γ a ha ≫ τg y γ a ha) ≫ yg y γ a ha)
    rw [Category.assoc, τg_yg]
    exact h0
  · cases i with
    | left =>
      simp only [Scheme.IsLocallyDirected.openCover_f]
      change P (τg y γ a ha ≫ yg y γ a ha)
      rw [τg_yg]; exact h1
    | right =>
      simp only [Scheme.IsLocallyDirected.openCover_f]
      change P (ιg y γ a ha ≫ yg y γ a ha)
      rw [ιg_yg]; exact h1

theorem locallyOfFiniteType_yg [LocallyOfFiniteType y] : LocallyOfFiniteType (yg y γ a ha) :=
  of_openCover_yg y γ a ha @LocallyOfFiniteType inferInstance inferInstance

theorem smooth_yg [Smooth y] : Smooth (yg y γ a ha) :=
  of_openCover_yg y γ a ha @Smooth inferInstance inferInstance

theorem quasiCompact_yg [QuasiCompact y] : QuasiCompact (yg y γ a ha) := by
  haveI : CompactSpace Y := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mp ‹QuasiCompact y›
  refine (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ⟨?_⟩
  have h : (Set.univ : Set ↑(Yg y γ a ha)) =
      Set.range (ιg y γ a ha).base ∪ Set.range (τg y γ a ha).base := by
    ext p
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    exact cover y γ a ha p
  rw [h]
  exact (isCompact_range (ιg y γ a ha).base.hom.continuous).union
    (isCompact_range (τg y γ a ha).base.hom.continuous)

end Glue

section Separated

theorem range_comp_of_surjective {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : Function.Surjective f.base) : Set.range (f ≫ g).base = Set.range g.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f.base x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩

theorem isClosed_preimage_range_diagonal {S Y' Y₁ Y₂ P : Scheme.{u}} (y' : Y' ⟶ S)
    (i₁ : Y₁ ⟶ Y') (i₂ : Y₂ ⟶ Y') [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (y₁ : Y₁ ⟶ S) (y₂ : Y₂ ⟶ S) (h₁ : y₁ = i₁ ≫ y') (h₂ : y₂ = i₂ ≫ y')
    (u : P ⟶ Y₁) (v : P ⟶ Y₂) (hP : IsPullback u v i₁ i₂) (huv : u ≫ y₁ = v ≫ y₂)
    (hc : IsClosed (Set.range (pullback.lift u v huv).base)) :
    IsClosed ((pullback.map y₁ y₂ y' y' i₁ i₂ (𝟙 S) (by rw [Category.comp_id, h₁])
      (by rw [Category.comp_id, h₂])).base ⁻¹' Set.range (pullback.diagonal y').base) := by
  subst h₁ h₂
  rw [← Scheme.Pullback.range_snd]
  set e := pullbackDiagonalMapIdIso i₁ i₂ y'
  have h1 : e.inv ≫ pullback.snd _ _ = pullback.lift (pullback.fst i₁ i₂) (pullback.snd i₁ i₂)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullbackDiagonalMapIdIso_inv_snd_fst]
    · rw [Category.assoc, pullback.lift_snd, pullbackDiagonalMapIdIso_inv_snd_snd]
  have h2 : hP.isoPullback.hom ≫ pullback.lift (pullback.fst i₁ i₂) (pullback.snd i₁ i₂)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]) = pullback.lift u v huv := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have h3 : Set.range (pullback.snd (pullback.diagonal y') (pullback.map (i₁ ≫ y') (i₂ ≫ y') y' y' i₁ i₂
      (𝟙 S) (by rw [Category.comp_id]) (by rw [Category.comp_id]))).base =
      Set.range (pullback.lift u v huv).base := by
    rw [← h2, ← h1, range_comp_of_surjective _ _ hP.isoPullback.hom.surjective,
      range_comp_of_surjective _ _ e.inv.surjective]
  rw [h3]
  exact hc

theorem exists_open_subset_compl {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (φ : A → B)
    (hφ : IsOpenMap φ) (D : Set B) (hD : IsClosed (φ ⁻¹' D)) (q : B) (hq : q ∈ Set.range φ)
    (hqD : q ∉ D) : ∃ O : Set B, O ⊆ Dᶜ ∧ IsOpen O ∧ q ∈ O := by
  obtain ⟨z, rfl⟩ := hq
  refine ⟨φ '' (φ ⁻¹' D)ᶜ, ?_, hφ _ hD.isOpen_compl, ⟨z, hqD, rfl⟩⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hw

theorem isClosed_range_diagonal_of_two_charts {S Y' Y₁ Y₂ : Scheme.{u}} (y' : Y' ⟶ S)
    (i₁ : Y₁ ⟶ Y') (i₂ : Y₂ ⟶ Y') [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (y₁ : Y₁ ⟶ S) (y₂ : Y₂ ⟶ S) (e₁ : y₁ = i₁ ≫ y') (e₂ : y₂ = i₂ ≫ y')
    (hcov : ∀ p : Y', p ∈ Set.range i₁.base ∨ p ∈ Set.range i₂.base)
    (H₁₁ : IsClosed ((pullback.map y₁ y₁ y' y' i₁ i₁ (𝟙 S) (by rw [Category.comp_id, e₁])
      (by rw [Category.comp_id, e₁])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₁₂ : IsClosed ((pullback.map y₁ y₂ y' y' i₁ i₂ (𝟙 S) (by rw [Category.comp_id, e₁])
      (by rw [Category.comp_id, e₂])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₂₁ : IsClosed ((pullback.map y₂ y₁ y' y' i₂ i₁ (𝟙 S) (by rw [Category.comp_id, e₂])
      (by rw [Category.comp_id, e₁])).base ⁻¹' Set.range (pullback.diagonal y').base))
    (H₂₂ : IsClosed ((pullback.map y₂ y₂ y' y' i₂ i₂ (𝟙 S) (by rw [Category.comp_id, e₂])
      (by rw [Category.comp_id, e₂])).base ⁻¹' Set.range (pullback.diagonal y').base)) :
    IsClosed (Set.range (pullback.diagonal y').base) := by
  subst e₁ e₂
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  rw [Set.mem_compl_iff] at hq

  have key : ∀ {Y₃ Y₄ : Scheme.{u}} (i₃ : Y₃ ⟶ Y') (i₄ : Y₄ ⟶ Y') [IsOpenImmersion i₃] [IsOpenImmersion i₄],
      IsClosed ((pullback.map (i₃ ≫ y') (i₄ ≫ y') y' y' i₃ i₄ (𝟙 S) (by rw [Category.comp_id])
        (by rw [Category.comp_id])).base ⁻¹' Set.range (pullback.diagonal y').base) →
      (pullback.fst y' y').base q ∈ Set.range i₃.base → (pullback.snd y' y').base q ∈ Set.range i₄.base →
      ∃ O : Set ↑(pullback y' y'), O ⊆ (Set.range (pullback.diagonal y').base)ᶜ ∧ IsOpen O ∧ q ∈ O := by
    intro Y₃ Y₄ i₃ i₄ _ _ H h₃ h₄
    refine exists_open_subset_compl _ (Scheme.Hom.isOpenEmbedding _).isOpenMap _ H q ?_ hq
    rw [Scheme.Pullback.range_map]
    exact ⟨h₃, h₄⟩
  rcases hcov ((pullback.fst y' y').base q) with h₃ | h₃ <;>
    rcases hcov ((pullback.snd y' y').base q) with h₄ | h₄
  · exact key i₁ i₁ H₁₁ h₃ h₄
  · exact key i₁ i₂ H₁₂ h₃ h₄
  · exact key i₂ i₁ H₂₁ h₃ h₄
  · exact key i₂ i₂ H₂₂ h₃ h₄

end Separated

section SeparatedGlue

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
variable [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]

theorem isSeparated_yg [IsClosedImmersion γ] [IsSeparated y] : IsSeparated (yg y γ a ha) := by
  have hcov : ∀ p : ↑(Yg y γ a ha), p ∈ Set.range (τg y γ a ha).base ∨ p ∈ Set.range (ιg y γ a ha).base :=
    fun p => (cover y γ a ha p).symm

  have hdiag : IsClosed (Set.range (pullback.lift (𝟙 Y) (𝟙 Y) rfl : Y ⟶ pullback y y).base) :=
    (pullback.diagonal y).isClosedEmbedding.isClosed_range
  have hpb := isPullback_τg_ιg y γ a ha

  have hlift : pullback.lift (pτ y γ a ha) (pι y γ a ha) (pτ_y y γ a ha) = cA y γ a ha := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pτ_def]
    · rw [pullback.lift_snd, pι_def]
  have hc12 : IsClosed (Set.range (pullback.lift (pτ y γ a ha) (pι y γ a ha) (pτ_y y γ a ha)).base) := by
    rw [hlift]
    exact (cA y γ a ha).isClosedEmbedding.isClosed_range
  have hlift' : pullback.lift (pι y γ a ha) (pτ y γ a ha) (pτ_y y γ a ha).symm =
      cA y γ a ha ≫ (pullbackSymmetry y y).hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSymmetry_hom_comp_fst, pι_def]
    · rw [pullback.lift_snd, Category.assoc, pullbackSymmetry_hom_comp_snd, pτ_def]
  have hc21 : IsClosed (Set.range (pullback.lift (pι y γ a ha) (pτ y γ a ha) (pτ_y y γ a ha).symm).base) := by
    rw [hlift']
    exact (cA y γ a ha ≫ (pullbackSymmetry y y).hom).isClosedEmbedding.isClosed_range
  refine ⟨IsClosedImmersion.of_isPreimmersion _ (isClosed_range_diagonal_of_two_charts (yg y γ a ha)
    (τg y γ a ha) (ιg y γ a ha) y y (τg_yg y γ a ha).symm (ιg_yg y γ a ha).symm hcov ?_ ?_ ?_ ?_)⟩
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (τg y γ a ha) (τg y γ a ha) y y
      (τg_yg y γ a ha).symm (τg_yg y γ a ha).symm (𝟙 Y) (𝟙 Y) (IsKernelPair.id_of_mono _) rfl hdiag
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (τg y γ a ha) (ιg y γ a ha) y y
      (τg_yg y γ a ha).symm (ιg_yg y γ a ha).symm _ _ hpb (pτ_y y γ a ha) hc12
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (ιg y γ a ha) (τg y γ a ha) y y
      (ιg_yg y γ a ha).symm (τg_yg y γ a ha).symm _ _ hpb.flip (pτ_y y γ a ha).symm hc21
  · exact isClosed_preimage_range_diagonal (yg y γ a ha) (ιg y γ a ha) (ιg y γ a ha) y y
      (ιg_yg y γ a ha).symm (ιg_yg y γ a ha).symm (𝟙 Y) (𝟙 Y) (IsKernelPair.id_of_mono _) rfl hdiag

end SeparatedGlue

section Points

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

abbrev grm : (U : Scheme.{u}) ⟶ Y3 y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

variable (g₀ : (U : Scheme.{u}) ⟶ G) (hg₀ : g₀ ≫ γ = grm y U m)

def mkΓa {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    T ⟶ Ga y γ a ha :=
  pullback.lift (w ≫ g₀)
    (pullback.lift (f := y) (g := y) x (w ≫ m.1)
      (by rw [Category.assoc, m.2, ← h2, Category.assoc, Category.assoc, pullback.condition]))
    (by
      rw [Category.assoc, hg₀]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
          exact h1
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
          exact h2
      · simp only [Category.assoc, pullback.lift_snd])

theorem mkΓa_pτ {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pτ y γ a ha = x := by
  rw [pτ_def, mkΓa, pullback.lift_snd_assoc, pullback.lift_fst]

theorem mkΓa_pι {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pι y γ a ha = w ≫ m.1 := by
  rw [pι_def, mkΓa, pullback.lift_snd_assoc, pullback.lift_snd]

include hg₀ in

theorem translate [IsOpenImmersion (pτ y γ a ha)] [IsOpenImmersion (pι y γ a ha)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
    (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y))
    (hw₁ : w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a) (hw₂ : w.1 ≫ U.ι ≫ pullback.snd y y = x.1) :
    x.1 ≫ τg y γ a ha = w.1 ≫ m.1 ≫ ιg y γ a ha := by
  have h1 : w.1 ≫ U.ι ≫ pullback.fst y y = x.1 ≫ y ≫ a := by rw [hw₁, reassoc_of% x.2]
  rw [← mkΓa_pτ y U m γ a ha g₀ hg₀ x.1 w.1 h1 hw₂, Category.assoc, pushout.condition, ← Category.assoc,
    mkΓa_pι, Category.assoc]

include hg₀ in

theorem exists_pτ_eq_and_exists_pι_eq [IsSeparated y] (u : ↑(U : Scheme.{u}))
    (hu : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base) :
    (∃ g : ↑(Ga y γ a ha), (pτ y γ a ha).base g = (U.ι ≫ pullback.snd y y).base u) ∧
      (∃ g : ↑(Ga y γ a ha), (pι y γ a ha).base g = m.1.base u) := by

  haveI : IsClosedImmersion (a ≫ y) := by rw [ha]; infer_instance
  haveI : IsClosedImmersion a := IsClosedImmersion.of_comp a y

  set w : Spec ((U : Scheme.{u}).residueField u) ⟶ (U : Scheme.{u}) := (U : Scheme.{u}).fromSpecResidueField u
  have hrange : Set.range (w ≫ U.ι ≫ pullback.fst y y).base ⊆ Set.range a.base := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hu
  obtain ⟨α, hα⟩ := exists_lift_of_isClosedImmersion (w ≫ U.ι ≫ pullback.fst y y) a hrange
  have h1 : w ≫ U.ι ≫ pullback.fst y y = (w ≫ U.ι ≫ pullback.snd y y) ≫ y ≫ a := by
    have hα' : α = (w ≫ U.ι ≫ pullback.snd y y) ≫ y := by
      rw [← Category.comp_id α, ← ha, ← Category.assoc, hα, Category.assoc, Category.assoc, Category.assoc,
        Category.assoc, pullback.condition]
    rw [← hα, hα', Category.assoc]
  set z := mkΓa y U m γ a ha g₀ hg₀ _ w h1 rfl
  refine ⟨⟨z.base (IsLocalRing.closedPoint _), ?_⟩, ⟨z.base (IsLocalRing.closedPoint _), ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, mkΓa_pτ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rw [← Scheme.Hom.comp_apply, mkΓa_pι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

include hg₀ in

theorem preimage_jA_subset_range_pτ [IsSeparated y] :
    (jA y a ha).base ⁻¹' (U : Set ↑(pullback y y)) ⊆ Set.range (pτ y γ a ha).base := by
  intro b hb
  have hu : (U.ι ≫ pullback.fst y y).base (⟨(jA y a ha).base b, hb⟩ : ↑(U : Scheme.{u})) ∈ Set.range a.base := by
    refine ⟨y.base b, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    change (y ≫ a).base b = (pullback.fst y y).base ((jA y a ha).base b)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨⟨g, hg⟩, -⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu
  refine ⟨g, ?_⟩
  rw [hg, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  change (pullback.snd y y).base ((jA y a ha).base b) = b
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

include hg₀ in

theorem preimage_jA_range_subset_range_pι [IsSeparated y] :
    (jA y a ha).base ⁻¹' Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)).base ⊆ Set.range (pι y γ a ha).base := by
  rintro c ⟨u, hu⟩
  have hu' : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base := by
    refine ⟨y.base c, ?_⟩
    rw [← pullback.lift_fst (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm),
      Scheme.Hom.comp_apply, hu]
    change (y ≫ a).base c = (pullback.fst y y).base ((jA y a ha).base c)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨-, ⟨g, hg⟩⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu'
  refine ⟨g, ?_⟩
  rw [hg, ← pullback.lift_snd (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm),
    Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

end Points

section Density

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

theorem mem_of_dense_fibre [TopologicalSpace.NoetherianSpace Y] (W : Set Y) (hW : IsOpen W)
    (s : Spec (CommRingCat.of R)) (hd : Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W))
    (x : Y) (hxs : y.base x = s) (hmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x) : x ∈ W := by
  set e := y.fiberι s with he
  have hemb : Topology.IsEmbedding e.base := e.isEmbedding
  have hrange : Set.range e.base = y.base ⁻¹' {s} := y.range_fiberι s
  obtain ⟨ξ, hξ⟩ : x ∈ Set.range e.base := by rw [hrange]; exact hxs
  haveI : TopologicalSpace.NoetherianSpace ↑(y.fiber s) := hemb.isInducing.noetherianSpace

  have hd' : Dense (e.base ⁻¹' W) := by
    rw [hemb.isInducing.dense_iff]
    intro ζ
    have hζ : e.base ζ ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ζ, rfl⟩
    have h1 : (⟨e.base ζ, hζ⟩ : {b : ↑Y // y.base b = s}) ∈
        closure ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W) := hd _
    rw [closure_subtype] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨⟨b, hb⟩, hbW, rfl⟩
    obtain ⟨ζ', rfl⟩ : b ∈ Set.range e.base := by rw [hrange]; exact hb
    exact ⟨ζ', hbW, rfl⟩
  have hmax' : ∀ ξ' : ↑(y.fiber s), ξ' ⤳ ξ → ξ' = ξ := by
    intro ξ' hξ'
    apply hemb.injective
    rw [hξ]
    refine hmax _ (hξ ▸ hξ'.map e.base.hom.continuous) ?_
    have h1 : e.base ξ' ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ξ', rfl⟩
    rw [h1, hxs]
  have := mem_of_dense_of_forall_specializes (e.base.hom.continuous.isOpen_preimage W hW) hd' ξ hmax'
  rwa [Set.mem_preimage, hξ] at this

variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

theorem dense_fibre_jA [IsSeparated y] (S : Set ↑(pullback y y)) (s : Spec (CommRingCat.of R))
    (hS : Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) := by

  haveI : IsClosedImmersion (jA y a ha ≫ pullback.snd y y) := by rw [pullback.lift_snd]; infer_instance
  haveI : IsClosedImmersion (jA y a ha) := IsClosedImmersion.of_comp (jA y a ha) (pullback.snd y y)
  have hainj : Function.Injective a.base := by
    intro s₁ s₂ h
    have := congrArg y.base h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha] at this

  let φ : {b : ↑Y // y.base b = s} → {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} :=
    fun b => ⟨(jA y a ha).base b.1, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, b.2]⟩
  have hφc : Continuous φ := ((jA y a ha).base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Topology.IsInducing φ := by
    refine Topology.IsInducing.of_comp hφc continuous_subtype_val ?_
    exact (jA y a ha).isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hE : pullback.fst (pullback.fst y y) a = (pullback.fst (pullback.fst y y) a ≫ pullback.snd y y) ≫ jA y a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.condition, Category.assoc, ← pullback.condition_assoc,
        reassoc_of% (pullback.condition (f := pullback.fst y y) (g := a)), reassoc_of% ha]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ : q ∈ Set.range (pullback.fst (pullback.fst y y) a).base := by
      rw [Scheme.Pullback.range_fst]; exact ⟨s, hq.symm⟩
    refine ⟨⟨(pullback.snd y y).base q, hainj ?_⟩, ?_⟩
    · change a.base (y.base ((pullback.snd y y).base q)) = a.base s
      congr 1
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ha]
      rfl
    · apply Subtype.ext
      change (jA y a ha).base ((pullback.snd y y).base q) = q
      conv_rhs => rw [← hz, hE]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  have hpre : ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) =
      φ ⁻¹' ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} → ↑(pullback y y)) ⁻¹' S) :=
    rfl
  rw [hpre, hφi.dense_iff]
  intro b
  rw [Set.image_preimage_eq _ hφs, hS.closure_eq]
  exact Set.mem_univ _

end Density

end P2mGlueTranslate534
p2m_reactivate "P2MW.S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section.P2mGlueTranslate534"

open P2mGlueTranslate534 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hγ : Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base ⊆
      Set.range γ.base)
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _) :
    ∃ (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧ IsOpenImmersion τ.1 ∧
      (∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base) ∧
      IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
          (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1) := by

  haveI := isOpenImmersion_pτ y γ a ha
  haveI := isOpenImmersion_pι y γ a ha

  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
  haveI : CompactSpace ↑Y := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mp ‹QuasiCompact y›
  haveI : IsNoetherian Y := {}
  haveI : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫ y)
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hγ

  refine ⟨Yg y γ a ha, yg y γ a ha, ⟨ιg y γ a ha, ιg_yg y γ a ha⟩, ⟨τg y γ a ha, τg_yg y γ a ha⟩,
    smooth_yg y γ a ha, isSeparated_yg y γ a ha, locallyOfFiniteType_yg y γ a ha, quasiCompact_yg y γ a ha,
    inferInstance, inferInstance, cover y γ a ha, ?_, ?_, isPullback_τg_ιg y γ a ha,
    fun t x w hw₁ hw₂ => translate y U m γ a ha g₀ hg₀ t x w hw₁ hw₂⟩
  ·
    intro p hp
    rcases cover y γ a ha p with h | ⟨x, rfl⟩
    · exact h
    have hxmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x := by
      intro x' h1 h2
      apply (τg y γ a ha).isOpenEmbedding.injective
      refine hp _ (h1.map (τg y γ a ha).base.hom.continuous) ?_
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, τg_yg]
      exact h2
    have hx : x ∈ Set.range (pτ y γ a ha).base :=
      mem_of_dense_fibre y _ (pτ y γ a ha).isOpenEmbedding.isOpen_range (y.base x)
        ((dense_fibre_jA y a ha _ _ (hU₁ (a.base (y.base x)))).mono
          (Set.preimage_mono (preimage_jA_subset_range_pτ y U m γ a ha g₀ hg₀))) x rfl hxmax
    obtain ⟨g, rfl⟩ := hx
    refine ⟨(pι y γ a ha).base g, ?_⟩
    change (ιg y γ a ha).base ((pι y γ a ha).base g) = (τg y γ a ha).base ((pτ y γ a ha).base g)
    rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply]
  ·
    intro p hp
    rcases cover y γ a ha p with ⟨z, rfl⟩ | h
    swap
    · exact h
    have hzmax : ∀ z' : Y, z' ⤳ z → y.base z' = y.base z → z' = z := by
      intro z' h1 h2
      apply (ιg y γ a ha).isOpenEmbedding.injective
      refine hp _ (h1.map (ιg y γ a ha).base.hom.continuous) ?_
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ιg_yg]
      exact h2
    have hz : z ∈ Set.range (pι y γ a ha).base :=
      mem_of_dense_fibre y _ (pι y γ a ha).isOpenEmbedding.isOpen_range (y.base z)
        ((dense_fibre_jA y a ha _ _ (hΦ₁ (a.base (y.base z)))).mono
          (Set.preimage_mono (preimage_jA_range_subset_range_pι y U m γ a ha g₀ hg₀))) z rfl hzmax
    obtain ⟨g, rfl⟩ := hz
    refine ⟨(pτ y γ a ha).base g, ?_⟩
    change (τg y γ a ha).base ((pτ y γ a ha).base g) = (ιg y γ a ha).base ((pι y γ a ha).base g)
    rw [← Scheme.Hom.comp_apply, pushout.condition, Scheme.Hom.comp_apply]

end
end S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
end P2MW
export P2MW.S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section (solution)
