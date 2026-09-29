-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_one_and_levelOne_axioms_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6c1d88ca-58b7-56eb-922f-260cfea981f6

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_one_and_levelOne_axioms_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (L : RelativeGroupLaw S f) {ι : Type u} (act : ι → (A ⟶ A)) (act_over : ∀ i : ι, act i ≫ f = f)
    (act_hom : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act i) (act_over i) (L.mul t P Q) = L.mul t (pushPt (act i) (act_over i) P) (pushPt (act i) (act_over i) Q)) :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P → FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 Q →
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.mul t P Q) ∧
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.inv t P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (L.one t)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P → nsmulPt L t 1 P = L.one t) ∧
    (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P →
        FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (pushPt (act i) (act_over i) P)) ∧
    IsFinite ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    Flat ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    LocallyOfFinitePresentation ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f).finrank s = 1 ^ 2) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), ((1 : ℕ) : k) ≠ 0 →
      ∃ e : ZMod 1 × ZMod 1 ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P},
        ∀ x y : ZMod 1 × ZMod 1,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) := by

  have he : (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f = 𝟙 (Spec (CommRingCat.of S)) :=
    (L.one (𝟙 (Spec (CommRingCat.of S)))).2

  have hnat : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
      t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 = (L.one t).1 := by
    intro T t
    have h := L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id t)
    exact congrArg Subtype.val h

  have key : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P ↔ P = L.one t := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      have hP₀t : P₀ = t := by
        have h1 := congrArg (fun g => g ≫ f) hP₀
        simp only [Category.assoc, he, Category.comp_id] at h1
        rw [h1]; exact P.2
      apply Subtype.ext
      rw [← hP₀, hP₀t]
      exact hnat t
    · rintro rfl
      exact ⟨t, hnat t⟩

  have hinv_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), L.inv t (L.one t) = L.one t := by
    intro T t
    rw [← L.mul_one t (L.inv t (L.one t)), L.inv_mul_cancel]
  have hpush_one : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
      pushPt (act i) (act_over i) (L.one t) = L.one t := by
    intro i T t
    have h := act_hom i t (L.one t) (L.one t)
    rw [L.one_mul] at h

    set x := pushPt (act i) (act_over i) (L.one t) with hx
    calc x = L.mul t (L.inv t x) (L.mul t x x) := by rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      _ = L.mul t (L.inv t x) x := by rw [← h]
      _ = L.one t := L.inv_mul_cancel t x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by
      rw [he]; infer_instance
    exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of S)))).1 f
  · intro T t P Q hP hQ
    rw [key] at hP hQ ⊢
    rw [key]
    subst hP hQ
    exact ⟨L.one_mul t _, hinv_one t⟩
  · intro T t
    exact (key t _).2 rfl
  · intro T t P hP
    rw [key] at hP
    subst hP
    show L.mul t (L.one t) (L.one t) = L.one t
    exact L.one_mul t _
  · intro i T t P hP
    rw [key] at hP ⊢
    subst hP
    exact hpush_one i t
  · rw [he]; infer_instance
  · rw [he]; infer_instance
  · rw [he]; infer_instance
  · intro s
    rw [he, Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  · intro k _ _ sk _
    refine ⟨{ toFun := fun _ => ⟨L.one (geomPoint k sk), (key _ _).2 rfl⟩
              invFun := fun _ => 0
              left_inv := fun x => Subsingleton.elim _ _
              right_inv := fun P => ?_ }, ?_⟩
    · apply Subtype.ext
      exact ((key _ _).1 P.2).symm
    · intro x y
      simp only [Equiv.coe_fn_mk]
      exact (L.one_mul _ _).symm

end S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_one_and_levelOne_axioms_of_isSeparated
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_one_and_levelOne_axioms_of_isSeparated (solution)
