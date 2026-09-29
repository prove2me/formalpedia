-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cf72688b-9068-5938-8f37-dee7bb997e6f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace DescB

theorem baseChange_mul_fst {S S' : Type} [CommRing S] [CommRing S']
    (u : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (pullback.snd f u)) :
    ((G.baseChange u).mul t' x y).1 ≫ pullback.fst f u =
      (G.mul (t' ≫ u)
        ⟨x.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul u G t' x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
  exact h

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end DescB

open DescB in
theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (φ₁ : R₁ →+* R) (φ₂ : R₂ →+* R) (ψ : R₁ →+* R₂) (hψ : φ₂.comp ψ = φ₁)
    (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (L₁ : RelativeGroupLaw R₁ f₁) (hA₁ : AbelianSchemePropertyBundle R₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom φ₁)))
    (hLa₁ : (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ₁))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1)) :
    ∃ (A₂ : Scheme.{0}) (f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)) (L₂ : RelativeGroupLaw R₂ f₂) (_ : AbelianSchemePropertyBundle R₂ f₂)
      (a₂ : A ⟶ A₂) (ha₂ : IsPullback a₂ f f₂ (Spec.map (CommRingCat.ofHom φ₂)))
      (b : A₂ ⟶ A₁) (hb : IsPullback b f₂ f₁ (Spec.map (CommRingCat.ofHom ψ))) (_ : a₂ ≫ b = a₁),
      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₂ = (L₂.mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ b = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom ψ))
        ⟨P.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, Q.2]⟩).1) := by
  have hSpec : Spec.map (CommRingCat.ofHom φ₁) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  let ι := Spec.map (CommRingCat.ofHom ψ)
  have hP := IsPullback.of_hasPullback f₁ ι

  let a₂ : A ⟶ pullback f₁ ι := pullback.lift a₁ (f ≫ Spec.map (CommRingCat.ofHom φ₂))
    (by rw [ha₁.w, hSpec, Category.assoc])
  have ha₂fst : a₂ ≫ pullback.fst f₁ ι = a₁ := pullback.lift_fst _ _ _
  have ha₂snd : a₂ ≫ pullback.snd f₁ ι = f ≫ Spec.map (CommRingCat.ofHom φ₂) := pullback.lift_snd _ _ _
  have ha₂ : IsPullback a₂ f (pullback.snd f₁ ι) (Spec.map (CommRingCat.ofHom φ₂)) := by
    refine IsPullback.of_right ?_ ha₂snd hP
    rw [ha₂fst, ← hSpec]
    exact ha₁
  refine ⟨pullback f₁ ι, pullback.snd f₁ ι, L₁.baseChange ι,
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback hA₁ hP, a₂, ha₂, pullback.fst f₁ ι, hP, ha₂fst, ?_, ?_⟩
  · intro T t P Q
    apply pullback.hom_ext
    · rw [Category.assoc, ha₂fst, hLa₁ T t P Q, baseChange_mul_fst]
      exact mul_val_congr L₁ (by rw [hSpec, Category.assoc]) _ _ _ _
        (show P.1 ≫ a₁ = (P.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
        (show Q.1 ≫ a₁ = (Q.1 ≫ a₂) ≫ pullback.fst f₁ ι by rw [Category.assoc, ha₂fst])
    · have h1 : (L.mul t P Q).1 ≫ a₂ ≫ pullback.snd f₁ ι = t ≫ Spec.map (CommRingCat.ofHom φ₂) := by
        rw [ha₂snd, ← Category.assoc, (L.mul t P Q).2]
      rw [Category.assoc]
      symm
      refine Eq.trans ?_ h1.symm
      exact ((L₁.baseChange ι).mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
        ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).2
  · intro T t P Q
    exact baseChange_mul_fst ι L₁ t P Q

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq (solution)
