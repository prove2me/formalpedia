-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_comp_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/44e9e15c-4e11-5a5a-944a-c9844023a9c5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

namespace BenchQBC

variable {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g : A' ⟶ A}
  (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))

def push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)} (x : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B))) f :=
  ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩

private noncomputable def _root_.BenchQBC.lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)}
    (z : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B))) f) : SchemeHomOver t' f' :=
  ⟨hg.lift z.1 t' z.2, hg.lift_snd _ _ _⟩

p2m_export "BenchQBC" "lift"
@[scoped simp] theorem push_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)} (x : SchemeHomOver t' f') :
    (push hg x).1 = x.1 ≫ g := rfl

@[scoped simp] theorem lift_coe_g {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)}
    (z : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B))) f) : (lift hg z).1 ≫ g = z.1 :=
  hg.lift_fst _ _ _

@[scoped simp] theorem push_lift {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)}
    (z : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B))) f) : push hg (lift hg z) = z :=
  Subtype.ext (hg.lift_fst _ _ _)

@[scoped simp] theorem lift_push {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)} (x : SchemeHomOver t' f') :
    lift hg (push hg x) = x := by
  apply Subtype.ext
  apply hg.hom_ext
  · rw [lift_coe_g]; rfl
  · rw [(lift hg (push hg x)).2, x.2]

theorem push_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of B)} :
    Function.Injective (push hg (T := T) (t' := t')) := by
  intro x y h
  rw [← lift_push hg x, ← lift_push hg y, h]

theorem push_comp {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B)) (t' : T' ⟶ Spec (CommRingCat.of B))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f') :
    push hg (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (show ψ ≫ t ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
        t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) by rw [← Category.assoc, hψ]) (push hg x) :=
  Subtype.ext (Category.assoc _ _ _)

noncomputable def law (L : RelativeGroupLaw S f) : RelativeGroupLaw B f' where
  mul t x y := lift hg (L.mul _ (push hg x) (push hg y))
  one t := lift hg (L.one _)
  inv t x := lift hg (L.inv _ (push hg x))
  mul_assoc t x y z := by simp only [push_lift, L.mul_assoc]
  one_mul t x := by simp only [push_lift, L.one_mul, lift_push]
  mul_one t x := by simp only [push_lift, L.mul_one, lift_push]
  inv_mul_cancel t x := by simp only [push_lift, L.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply push_injective hg
    rw [push_comp, push_lift, push_lift, L.mul_natural _ _ ψ, push_comp, push_comp]

end BenchQBC
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback.BenchQBC"

theorem solution
    {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] {A A' : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
    (L : RelativeGroupLaw S f) :
    ∃ L' : RelativeGroupLaw B f',
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ g =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)))
            ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B)),
        (L'.one t').1 ≫ g = (L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)))).1) ∧
      (L.IsCommutative → L'.IsCommutative) := by
  refine ⟨BenchQBC.law hg L, ?_, ?_, ?_⟩
  · intro T t' x y
    exact BenchQBC.lift_coe_g hg _
  · intro T t'
    exact BenchQBC.lift_coe_g hg _
  · intro hc T t x y
    show BenchQBC.lift hg (L.mul _ (BenchQBC.push hg x) (BenchQBC.push hg y)) =
      BenchQBC.lift hg (L.mul _ (BenchQBC.push hg y) (BenchQBC.push hg x))
    rw [hc.mul_comm]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback (solution)
