-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e89e185f-8619-526e-b3fd-7cde583c4d1d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GroupLawSpread

section Prod

variable {X X₀ B B₀ : Scheme.{0}} (fX : X ⟶ B) (f₀ : X₀ ⟶ B₀) (g : X ⟶ X₀) (s : B ⟶ B₀)

noncomputable def prodMap (hg : IsPullback g fX f₀ s) : pullback fX fX ⟶ pullback f₀ f₀ :=
  pullback.lift (pullback.fst fX fX ≫ g) (pullback.snd fX fX ≫ g)
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])

@[scoped simp] theorem prodMap_fst (hg : IsPullback g fX f₀ s) : prodMap fX f₀ g s hg ≫ pullback.fst f₀ f₀ = pullback.fst fX fX ≫ g :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem prodMap_snd (hg : IsPullback g fX f₀ s) : prodMap fX f₀ g s hg ≫ pullback.snd f₀ f₀ = pullback.snd fX fX ≫ g :=
  pullback.lift_snd _ _ _

theorem prod_isPullback (hg : IsPullback g fX f₀ s) :
    IsPullback (prodMap fX f₀ g s hg) (pullback.fst fX fX ≫ fX) (pullback.fst f₀ f₀ ≫ f₀) s := by

  have Q1 : IsPullback (pullback.snd fX fX) (pullback.fst fX fX) fX fX := (IsPullback.of_hasPullback fX fX).flip
  have R1 : IsPullback (pullback.snd fX fX ≫ g) (pullback.fst fX fX) f₀ (fX ≫ s) := Q1.paste_horiz hg
  have Q2 : IsPullback (pullback.snd f₀ f₀) (pullback.fst f₀ f₀) f₀ f₀ := (IsPullback.of_hasPullback f₀ f₀).flip
  have R1' : IsPullback (prodMap fX f₀ g s hg ≫ pullback.snd f₀ f₀) (pullback.fst fX fX) f₀ (g ≫ f₀) := by
    rw [prodMap_snd, hg.w]; exact R1
  have s' : IsPullback (prodMap fX f₀ g s hg) (pullback.fst fX fX) (pullback.fst f₀ f₀) g :=
    IsPullback.of_right R1' (prodMap_fst fX f₀ g s hg) Q2
  exact s'.paste_vert hg

end Prod

section Represent

variable {K : Type} [CommRing K] {A : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of K)} (LA : RelativeGroupLaw K fA)

noncomputable abbrev tAA (fA : A ⟶ Spec (CommRingCat.of K)) : pullback fA fA ⟶ Spec (CommRingCat.of K) := pullback.fst fA fA ≫ fA

noncomputable def U₁ (fA : A ⟶ Spec (CommRingCat.of K)) : SchemeHomOver (tAA fA) fA := ⟨pullback.fst fA fA, rfl⟩
noncomputable def U₂ (fA : A ⟶ Spec (CommRingCat.of K)) : SchemeHomOver (tAA fA) fA := ⟨pullback.snd fA fA, pullback.condition.symm⟩

noncomputable def mMor : pullback fA fA ⟶ A := (LA.mul (tAA fA) (U₁ fA) (U₂ fA)).1

theorem mMor_over : mMor LA ≫ fA = tAA fA := (LA.mul (tAA fA) (U₁ fA) (U₂ fA)).2

noncomputable def eMor : Spec (CommRingCat.of K) ⟶ A := (LA.one (𝟙 _)).1

theorem eMor_over : eMor LA ≫ fA = 𝟙 _ := (LA.one (𝟙 _)).2

noncomputable def iMor : A ⟶ A := (LA.inv fA ⟨𝟙 A, Category.id_comp _⟩).1

theorem iMor_over : iMor LA ≫ fA = fA := (LA.inv fA ⟨𝟙 A, Category.id_comp _⟩).2

noncomputable def pairPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of K)} (P Q : SchemeHomOver t fA) :
    T ⟶ pullback fA fA :=
  pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)

theorem pairPt_tAA {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of K)} (P Q : SchemeHomOver t fA) :
    pairPt P Q ≫ tAA fA = t := by
  rw [pairPt, tAA, ← Category.assoc, pullback.lift_fst, P.2]

theorem mul_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t fA) :
    (LA.mul t P Q).1 = pairPt P Q ≫ mMor LA := by
  have h := LA.mul_natural (tAA fA) t (pairPt P Q) (pairPt_tAA P Q) (U₁ fA) (U₂ fA)
  have h1 : schemeHomOverComp (pairPt P Q) (pairPt_tAA P Q) (U₁ fA) = P :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have h2 : schemeHomOverComp (pairPt P Q) (pairPt_tAA P Q) (U₂ fA) = Q :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [h1, h2] at h
  rw [← h]; rfl

theorem one_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) : (LA.one t).1 = t ≫ eMor LA := by
  have h := LA.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]; rfl

theorem inv_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t fA) :
    (LA.inv t P).1 = P.1 ≫ iMor LA := by
  letI := LA.pointGroup t

  have hψ : P.1 ≫ fA = t := P.2
  have hmul : ∀ x y : SchemeHomOver fA fA,
      schemeHomOverComp P.1 hψ (LA.mul fA x y) = LA.mul t (schemeHomOverComp P.1 hψ x) (schemeHomOverComp P.1 hψ y) :=
    LA.mul_natural fA t P.1 hψ
  have hone : schemeHomOverComp P.1 hψ (LA.one fA) = LA.one t := LA.one_natural fA t P.1 hψ
  have hid : schemeHomOverComp P.1 hψ ⟨𝟙 A, Category.id_comp _⟩ = P := Subtype.ext (Category.comp_id _)
  have key : LA.mul t (schemeHomOverComp P.1 hψ (LA.inv fA ⟨𝟙 A, Category.id_comp _⟩))
      (schemeHomOverComp P.1 hψ ⟨𝟙 A, Category.id_comp _⟩) = LA.one t := by
    rw [← hmul, LA.inv_mul_cancel, hone]
  rw [hid] at key
  have : schemeHomOverComp P.1 hψ (LA.inv fA ⟨𝟙 A, Category.id_comp _⟩) = LA.inv t P :=
    eq_inv_of_mul_eq_one_left key
  exact (congrArg Subtype.val this).symm

end Represent

section Main

theorem specMap_comp_of_pin {k K : Type} [Field k] [Field K] [Algebra k K]
    {L L'' : IntermediateField k K} (j : ↥L →+* ↥L'') (hj : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K)) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)) ≫ Spec.map (CommRingCat.ofHom j) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥L K)) := by
  have hcomp : (algebraMap ↥L'' K).comp j = algebraMap ↥L K := by
    ext x; exact hj x
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

theorem main
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of K)) (LA : RelativeGroupLaw K fA)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : A ⟶ X₀) (hg : IsPullback g fA f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lm : IntermediateField k K) (_ : FiniteDimensional k ↥Lm) (_ : L ≤ Lm),
      ∀ (L'' : IntermediateField k K) (_ : Lm ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : A ⟶ X₂) (hr : IsPullback r fA f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g),
        ∃ L₂ : RelativeGroupLaw ↥L'' f₂,
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' fA),
            (LA.mul t' P Q).1 ≫ r =
              (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
                ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1) ∧
          (LA.IsCommutative → L₂.IsCommutative) := by

  haveI : CompactSpace ↥X₀ := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := f₀)).mp inferInstance
  haveI : QuasiSeparatedSpace ↥X₀ := (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := f₀)).mp inferInstance
  haveI : CompactSpace ↥(pullback f₀ f₀) := inferInstance
  haveI : QuasiSeparatedSpace ↥(pullback f₀ f₀) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := pullback.fst f₀ f₀ ≫ f₀)).mp inferInstance

  have hgAA := prod_isPullback fA f₀ g (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))) hg
  obtain ⟨Lμ, hLμ, hLLμ, Hm⟩ :=
    AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic k K L
      (tAA fA) fA (pullback.fst f₀ f₀ ≫ f₀) f₀ _ hgAA g hg (mMor LA) (mMor_over LA)
  obtain ⟨Le, hLe, hLLe, He⟩ :=
    AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic k K L
      (𝟙 _) fA (𝟙 _) f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))) IsPullback.of_id_snd g hg
      (eMor LA) (eMor_over LA)
  obtain ⟨Li, hLi, hLLi, Hi⟩ :=
    AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic k K L
      fA fA f₀ f₀ g hg g hg (iMor LA) (iMor_over LA)
  refine ⟨Lμ ⊔ Le ⊔ Li, inferInstance, hLLμ.trans (le_sup_left.trans le_sup_left), ?_⟩
  intro L'' hL'' j hj X₂ f₂ r hr q hq hrq
  have hμ : Lμ ≤ L'' := (le_sup_left.trans le_sup_left).trans hL''
  have he : Le ≤ L'' := (le_sup_right.trans le_sup_left).trans hL''
  have hi : Li ≤ L'' := le_sup_right.trans hL''

  have hSpec := specMap_comp_of_pin j hj

  have hrAA := prod_isPullback fA f₂ r (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))) hr
  have hqAA := prod_isPullback f₂ f₀ q (Spec.map (CommRingCat.ofHom j)) hq
  have hcompAA : prodMap fA f₂ r _ hr ≫ prodMap f₂ f₀ q _ hq = prodMap fA f₀ g _ hg := by
    apply pullback.hom_ext
    · simp only [Category.assoc, prodMap_fst]; rw [← Category.assoc, prodMap_fst, Category.assoc, hrq]
    · simp only [Category.assoc, prodMap_snd]; rw [← Category.assoc, prodMap_snd, Category.assoc, hrq]
  obtain ⟨m₂, hm₂f, hm₂r⟩ := Hm L'' hμ j hj (pullback f₂ f₂) X₂ (pullback.fst f₂ f₂ ≫ f₂) f₂
    _ hrAA _ hqAA hcompAA r hr q hq hrq
  have sqS : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))) (𝟙 _) (𝟙 _)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))) := IsPullback.of_id_snd
  have sqj : IsPullback (Spec.map (CommRingCat.ofHom j)) (𝟙 (Spec (CommRingCat.of ↥L''))) (𝟙 _)
      (Spec.map (CommRingCat.ofHom j)) := IsPullback.of_id_snd
  obtain ⟨e₂, he₂f, he₂r⟩ := He L'' he j hj (Spec (CommRingCat.of ↥L'')) X₂ (𝟙 _) f₂
    (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))) sqS (Spec.map (CommRingCat.ofHom j)) sqj hSpec r hr q hq hrq
  obtain ⟨i₂, hi₂f, hi₂r⟩ := Hi L'' hi j hj X₂ X₂ f₂ f₂ r hr q hq hrq r hr q hq hrq

  let mul₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')),
      SchemeHomOver t f₂ → SchemeHomOver t f₂ → SchemeHomOver t f₂ := fun t P Q =>
    ⟨pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m₂, by
      rw [Category.assoc, hm₂f, ← Category.assoc, pullback.lift_fst, P.2]⟩
  let one₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')), SchemeHomOver t f₂ := fun t =>
    ⟨t ≫ e₂, by rw [Category.assoc, he₂f, Category.comp_id]⟩
  let inv₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')), SchemeHomOver t f₂ → SchemeHomOver t f₂ := fun t P =>
    ⟨P.1 ≫ i₂, by rw [Category.assoc, hi₂f, P.2]⟩
  have mul₂_natural : ∀ {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (t' : T' ⟶ Spec (CommRingCat.of ↥L''))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t f₂),
      schemeHomOverComp ψ hψ (mul₂ t x y) = mul₂ t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) := by
    intro T T' t t' ψ hψ x y
    apply Subtype.ext
    change ψ ≫ (pullback.lift x.1 y.1 _ ≫ m₂) = pullback.lift (ψ ≫ x.1) (ψ ≫ y.1) _ ≫ m₂
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have one₂_natural : ∀ {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (t' : T' ⟶ Spec (CommRingCat.of ↥L''))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), schemeHomOverComp ψ hψ (one₂ t) = one₂ t' := by
    intro T T' t t' ψ hψ
    apply Subtype.ext
    change ψ ≫ (t ≫ e₂) = t' ≫ e₂
    rw [← Category.assoc, hψ]
  have inv₂_natural : ∀ {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (t' : T' ⟶ Spec (CommRingCat.of ↥L''))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f₂),
      schemeHomOverComp ψ hψ (inv₂ t x) = inv₂ t' (schemeHomOverComp ψ hψ x) := by
    intro T T' t t' ψ hψ x
    apply Subtype.ext
    change ψ ≫ (x.1 ≫ i₂) = (ψ ≫ x.1) ≫ i₂
    rw [Category.assoc]

  let S := Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))
  let pushF : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of K)}, SchemeHomOver t' fA → SchemeHomOver (t' ≫ S) f₂ :=
    fun {T} {t'} X => ⟨X.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, X.2]⟩
  have push_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (X Y : SchemeHomOver t' fA),
      pushF (LA.mul t' X Y) = mul₂ (t' ≫ S) (pushF X) (pushF Y) := by
    intro T t' X Y
    apply Subtype.ext
    change (LA.mul t' X Y).1 ≫ r = pullback.lift (X.1 ≫ r) (Y.1 ≫ r) _ ≫ m₂
    rw [mul_eq LA t' X Y, Category.assoc, ← hm₂r, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, prodMap_fst, ← Category.assoc, pairPt, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, prodMap_snd, ← Category.assoc, pairPt, pullback.lift_snd, pullback.lift_snd]
  have push_one : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)), pushF (LA.one t') = one₂ (t' ≫ S) := by
    intro T t'
    apply Subtype.ext
    change (LA.one t').1 ≫ r = (t' ≫ S) ≫ e₂
    rw [one_eq LA t', Category.assoc, ← he₂r, Category.assoc]
  have push_inv : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (X : SchemeHomOver t' fA),
      pushF (LA.inv t' X) = inv₂ (t' ≫ S) (pushF X) := by
    intro T t' X
    apply Subtype.ext
    change (LA.inv t' X).1 ≫ r = (X.1 ≫ r) ≫ i₂
    rw [inv_eq LA t' X, Category.assoc, ← hi₂r, Category.assoc]

  have cov : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P : SchemeHomOver t f₂),
      ∃ X : SchemeHomOver (pullback.snd t S) fA,
        schemeHomOverComp (pullback.fst t S) pullback.condition P = pushF X := by
    intro T t P
    refine ⟨⟨hr.lift (pullback.fst t S ≫ P.1) (pullback.snd t S) (by rw [Category.assoc, P.2]; exact pullback.condition),
      hr.lift_snd _ _ _⟩, ?_⟩
    apply Subtype.ext
    change pullback.fst t S ≫ P.1 = hr.lift _ _ _ ≫ r
    rw [hr.lift_fst]
  have epi_cov : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')), Epi (pullback.fst t S) := by
    intro T t
    obtain ⟨h1, h2, -⟩ :=
      AlgebraicGeometry.surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
        (F := ↥L'') (Ω := K) (fX := pullback.snd t S) (f₀ := t) (pullback.fst t S) (IsPullback.of_hasPullback t S)
    exact Flat.epi_of_flat_of_surjective _

  let L₂ : RelativeGroupLaw ↥L'' f₂ :=
    { mul := mul₂
      one := one₂
      inv := inv₂
      mul_assoc := by
        intro T t x y z
        haveI := epi_cov t
        obtain ⟨X, hX⟩ := cov t x
        obtain ⟨Y, hY⟩ := cov t y
        obtain ⟨Z, hZ⟩ := cov t z
        apply Subtype.ext
        apply (cancel_epi (pullback.fst t S)).mp
        have h := congrArg Subtype.val
          (mul₂_natural t _ (pullback.fst t S) pullback.condition (mul₂ t x y) z)
        have h' := congrArg Subtype.val
          (mul₂_natural t _ (pullback.fst t S) pullback.condition x (mul₂ t y z))
        change pullback.fst t S ≫ (mul₂ t (mul₂ t x y) z).1 = pullback.fst t S ≫ (mul₂ t x (mul₂ t y z)).1
        refine h.trans (Eq.trans ?_ h'.symm)
        rw [mul₂_natural, mul₂_natural, hX, hY, hZ, ← push_mul, ← push_mul, ← push_mul, ← push_mul, LA.mul_assoc]
      one_mul := by
        intro T t x
        haveI := epi_cov t
        obtain ⟨X, hX⟩ := cov t x
        apply Subtype.ext
        apply (cancel_epi (pullback.fst t S)).mp
        have h := congrArg Subtype.val (mul₂_natural t _ (pullback.fst t S) pullback.condition (one₂ t) x)
        change pullback.fst t S ≫ (mul₂ t (one₂ t) x).1 = pullback.fst t S ≫ x.1
        refine h.trans ?_
        rw [one₂_natural, hX, ← push_one, ← push_mul, LA.one_mul]
        exact (congrArg Subtype.val hX).symm
      mul_one := by
        intro T t x
        haveI := epi_cov t
        obtain ⟨X, hX⟩ := cov t x
        apply Subtype.ext
        apply (cancel_epi (pullback.fst t S)).mp
        have h := congrArg Subtype.val (mul₂_natural t _ (pullback.fst t S) pullback.condition x (one₂ t))
        change pullback.fst t S ≫ (mul₂ t x (one₂ t)).1 = pullback.fst t S ≫ x.1
        refine h.trans ?_
        rw [one₂_natural, hX, ← push_one, ← push_mul, LA.mul_one]
        exact (congrArg Subtype.val hX).symm
      inv_mul_cancel := by
        intro T t x
        haveI := epi_cov t
        obtain ⟨X, hX⟩ := cov t x
        apply Subtype.ext
        apply (cancel_epi (pullback.fst t S)).mp
        have h := congrArg Subtype.val (mul₂_natural t _ (pullback.fst t S) pullback.condition (inv₂ t x) x)
        have h' := congrArg Subtype.val (one₂_natural t _ (pullback.fst t S) pullback.condition)
        change pullback.fst t S ≫ (mul₂ t (inv₂ t x) x).1 = pullback.fst t S ≫ (one₂ t).1
        refine h.trans (Eq.trans ?_ h'.symm)
        rw [inv₂_natural, hX, ← push_inv, ← push_mul, LA.inv_mul_cancel, push_one]
      mul_natural := mul₂_natural }
  refine ⟨L₂, ?_, ?_⟩
  · intro T t' P Q
    exact congrArg Subtype.val (push_mul t' P Q)
  · intro hc T t x y
    haveI := epi_cov t
    obtain ⟨X, hX⟩ := cov t x
    obtain ⟨Y, hY⟩ := cov t y
    apply Subtype.ext
    apply (cancel_epi (pullback.fst t S)).mp
    have h := congrArg Subtype.val (mul₂_natural t _ (pullback.fst t S) pullback.condition x y)
    have h' := congrArg Subtype.val (mul₂_natural t _ (pullback.fst t S) pullback.condition y x)
    change pullback.fst t S ≫ (mul₂ t x y).1 = pullback.fst t S ≫ (mul₂ t y x).1
    refine h.trans (Eq.trans ?_ h'.symm)
    rw [hX, hY, ← push_mul, ← push_mul, hc.mul_comm]

end Main

end GroupLawSpread
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap.GroupLawSpread"

theorem solution
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of K)) (LA : RelativeGroupLaw K fA)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : A ⟶ X₀) (hg : CategoryTheory.IsPullback g fA f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lm : IntermediateField k K) (_ : FiniteDimensional k ↥Lm) (_ : L ≤ Lm),
      ∀ (L'' : IntermediateField k K) (_ : Lm ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : A ⟶ X₂) (hr : CategoryTheory.IsPullback r fA f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : CategoryTheory.IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g),
        ∃ L₂ : RelativeGroupLaw ↥L'' f₂,
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' fA),
            (LA.mul t' P Q).1 ≫ r =
              (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
                ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1) ∧
          (LA.IsCommutative → L₂.IsCommutative) :=
  GroupLawSpread.main k K L fA LA f₀ g hg

end S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap (solution)
