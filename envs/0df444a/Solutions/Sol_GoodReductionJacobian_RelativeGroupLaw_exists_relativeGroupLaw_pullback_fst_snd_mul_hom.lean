-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_pullback_fst_snd_mul_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bb97982b-6e59-5da0-9c0c-6820b57da7ca

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw"
namespace P2mProductLaw
p2m_open "GoodReductionJacobian"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

def π₁ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (X : SchemeHomOver t (pullback.fst f f ≫ f)) : SchemeHomOver t f :=
  ⟨X.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact X.2⟩

def π₂ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (X : SchemeHomOver t (pullback.fst f f ≫ f)) : SchemeHomOver t f :=
  ⟨X.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact X.2⟩

noncomputable def pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t f) :
    SchemeHomOver t (pullback.fst f f ≫ f) :=
  ⟨pullback.lift a.1 b.1 (a.2.trans b.2.symm), by rw [← Category.assoc, pullback.lift_fst]; exact a.2⟩

@[scoped simp] theorem π₁_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (X : SchemeHomOver t (pullback.fst f f ≫ f)) :
    (π₁ f X).1 = X.1 ≫ pullback.fst f f := rfl
@[scoped simp] theorem π₂_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (X : SchemeHomOver t (pullback.fst f f ≫ f)) :
    (π₂ f X).1 = X.1 ≫ pullback.snd f f := rfl
@[scoped simp] theorem pair_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t f) :
    (pair f a b).1 = pullback.lift a.1 b.1 (a.2.trans b.2.symm) := rfl

@[scoped simp] theorem π₁_pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t f) : π₁ f (pair f a b) = a :=
  Subtype.ext (pullback.lift_fst _ _ _)
@[scoped simp] theorem π₂_pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver t f) : π₂ f (pair f a b) = b :=
  Subtype.ext (pullback.lift_snd _ _ _)

theorem pair_π {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (X : SchemeHomOver t (pullback.fst f f ≫ f)) :
    pair f (π₁ f X) (π₂ f X) = X :=
  Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))

theorem ext_π {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {X Y : SchemeHomOver t (pullback.fst f f ≫ f)}
    (h₁ : π₁ f X = π₁ f Y) (h₂ : π₂ f X = π₂ f Y) : X = Y :=
  Subtype.ext (pullback.hom_ext (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

theorem π₁_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (X : SchemeHomOver t (pullback.fst f f ≫ f)) : π₁ f (schemeHomOverComp ψ hψ X) = schemeHomOverComp ψ hψ (π₁ f X) :=
  Subtype.ext (Category.assoc _ _ _)
theorem π₂_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (X : SchemeHomOver t (pullback.fst f f ≫ f)) : π₂ f (schemeHomOverComp ψ hψ X) = schemeHomOverComp ψ hψ (π₂ f X) :=
  Subtype.ext (Category.assoc _ _ _)

variable (L : RelativeGroupLaw R f)

noncomputable def prodLaw : RelativeGroupLaw R (pullback.fst f f ≫ f) where
  mul t X Y := pair f (L.mul t (π₁ f X) (π₁ f Y)) (L.mul t (π₂ f X) (π₂ f Y))
  one t := pair f (L.one t) (L.one t)
  inv t X := pair f (L.inv t (π₁ f X)) (L.inv t (π₂ f X))
  mul_assoc t X Y Z := by
    apply ext_π f <;> simp only [π₁_pair, π₂_pair, L.mul_assoc]
  one_mul t X := by
    apply ext_π f <;> simp only [π₁_pair, π₂_pair, L.one_mul]
  mul_one t X := by
    apply ext_π f <;> simp only [π₁_pair, π₂_pair, L.mul_one]
  inv_mul_cancel t X := by
    apply ext_π f <;> simp only [π₁_pair, π₂_pair, L.inv_mul_cancel]
  mul_natural t t' ψ hψ X Y := by
    apply ext_π f
    · rw [π₁_comp, π₁_pair, π₁_pair, L.mul_natural, π₁_comp, π₁_comp]
    · rw [π₂_comp, π₂_pair, π₂_pair, L.mul_natural, π₂_comp, π₂_comp]

theorem prodLaw_mul (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (X Y : SchemeHomOver t (pullback.fst f f ≫ f)) :
    (prodLaw f L).mul t X Y = pair f (L.mul t (π₁ f X) (π₁ f Y)) (L.mul t (π₂ f X) (π₂ f Y)) := rfl

theorem prodLaw_one (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) : (prodLaw f L).one t = pair f (L.one t) (L.one t) := rfl

end GoodReductionJacobian.P2mProductLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian.P2mProductLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.GoodReductionJacobian.P2mProductLaw"

open GoodReductionJacobian.P2mProductLaw in

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) :
    ∃ LP : RelativeGroupLaw R (pullback.fst f f ≫ f),

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.fst f f =
            (L.mul t ⟨P.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact P.2⟩
              ⟨Q.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact Q.2⟩).1) ∧
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.snd f f =
            (L.mul t ⟨P.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact P.2⟩
              ⟨Q.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact Q.2⟩).1) ∧

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)),
          (LP.one t).1 ≫ pullback.fst f f = (L.one t).1 ∧ (LP.one t).1 ≫ pullback.snd f f = (L.one t).1) ∧

      (L.IsCommutative →
        ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 =
            (L.mul t
              ⟨P.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact P.2⟩
              ⟨Q.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact Q.2⟩).1) := by
  refine ⟨prodLaw f L, ?_, ?_, ?_, ?_⟩
  · intro S t P Q
    show (pair f _ _).1 ≫ pullback.fst f f = _
    rw [pair_coe, pullback.lift_fst]
    rfl
  · intro S t P Q
    show (pair f _ _).1 ≫ pullback.snd f f = _
    rw [pair_coe, pullback.lift_snd]
    rfl
  · intro S t
    exact ⟨by show (pair f _ _).1 ≫ pullback.fst f f = _; rw [pair_coe, pullback.lift_fst],
      by show (pair f _ _).1 ≫ pullback.snd f f = _; rw [pair_coe, pullback.lift_snd]⟩
  · intro hc S t P Q

    have hμ : ∀ X : SchemeHomOver t (pullback.fst f f ≫ f),
        X.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 =
          (L.mul t (π₁ f X) (π₂ f X)).1 := by
      intro X
      have h := L.mul_natural (pullback.fst f f ≫ f) t X.1 X.2 ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
      exact congrArg Subtype.val h
    have hP : (⟨P.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
        by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact P.2⟩ : SchemeHomOver t f) =
        L.mul t (π₁ f P) (π₂ f P) := Subtype.ext (hμ P)
    have hQ : (⟨Q.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
        by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact Q.2⟩ : SchemeHomOver t f) =
        L.mul t (π₁ f Q) (π₂ f Q) := Subtype.ext (hμ Q)
    rw [hμ, hP, hQ, prodLaw_mul, π₁_pair, π₂_pair]

    congr 1
    rw [L.mul_assoc, L.mul_assoc, ← L.mul_assoc t (π₁ f Q), hc t (π₁ f Q) (π₂ f P), L.mul_assoc]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom (solution)
