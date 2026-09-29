-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1289e829-637b-5183-bab8-070f63e81acf

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace LawUniqAux

open GoodReductionJacobian

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : SchemeHomOver t f)
    (h : G.mul t e e = e) : e = G.one t := by
  calc e = G.mul t (G.one t) e := (G.one_mul t e).symm
    _ = G.mul t (G.mul t (G.inv t e) e) e := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t e) (G.mul t e e) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t e) e := by rw [h]
    _ = G.one t := G.inv_mul_cancel t e

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y x : SchemeHomOver t f)
    (h : G.mul t y x = G.one t) : y = G.inv t x := by
  calc y = G.mul t y (G.one t) := (G.mul_one t y).symm
    _ = G.mul t y (G.mul t x (G.inv t x)) := by rw [G.mul_inv_cancel]
    _ = G.mul t (G.mul t y x) (G.inv t x) := by rw [G.mul_assoc]
    _ = G.mul t (G.one t) (G.inv t x) := by rw [h]
    _ = G.inv t x := G.one_mul t _

end LawUniqAux

open LawUniqAux in
theorem solution
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (L₁ L₂ : RelativeGroupLaw R' (pullback.snd f ι))
    (h₁ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₁.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h₂ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      (L₂.mul t' P Q).1 ≫ pullback.fst f ι =
        (G.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    L₁ = L₂ := by

  have hmul : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
      L₁.mul t' P Q = L₂.mul t' P Q := by
    intro T t' P Q
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [h₁ T t' P Q, h₂ T t' P Q]
    · rw [(L₁.mul t' P Q).2, (L₂.mul t' P Q).2]

  have hone : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')), L₁.one t' = L₂.one t' := by
    intro T t'
    apply eq_one_of_mul_self L₂
    rw [← hmul, L₁.one_mul]

  have hinv : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (pullback.snd f ι)),
      L₁.inv t' P = L₂.inv t' P := by
    intro T t' P
    apply eq_inv_of_mul_eq_one L₂
    rw [← hmul, L₁.inv_mul_cancel, hone]

  obtain ⟨mul₁, one₁, inv₁, ma₁, om₁, mo₁, im₁, mn₁⟩ := L₁
  obtain ⟨mul₂, one₂, inv₂, ma₂, om₂, mo₂, im₂, mn₂⟩ := L₂
  have hm : @mul₁ = @mul₂ := by
    funext T t' P Q
    exact hmul T t' P Q
  have ho : @one₁ = @one₂ := by
    funext T t'
    exact hone T t'
  have hi : @inv₁ = @inv₂ := by
    funext T t' P
    exact hinv T t' P
  subst hm ho hi
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_fst_eq (solution)
