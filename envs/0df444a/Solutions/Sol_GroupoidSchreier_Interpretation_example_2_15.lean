-- Prove2me | solution 1 for GroupoidSchreier.Interpretation.example_2_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:01:39.088768+00:00
-- url     : https://prove2.me/submissions/132b194b-9323-431f-9017-61344fd9adf6

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

open CategoryTheory

universe u

namespace Aux_GS215
open GroupoidSchreier.Interpretation

variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] (E : Extension G K)

lemma cancel1 {A B C : G} (f : E.Hom A B) (X : E.Hom C B) :
    E.comp f (E.comp (E.inv f) X) = X := by
  rw [← E.assoc, E.comp_inv, E.id_comp]

lemma cancel2 {A B C : G} (f : E.Hom A B) (X : E.Hom C A) :
    E.comp (E.inv f) (E.comp f X) = X := by
  rw [← E.assoc, E.inv_comp, E.id_comp]

lemma inv_id (A : G) : E.inv (E.id A) = E.id A := by
  have := E.comp_inv (E.id A)
  rwa [E.id_comp] at this

lemma iota_one (A : G) : E.ι A 1 = E.id A := by
  have h := E.ι_mul A 1 1
  rw [mul_one] at h
  have h2 : E.comp (E.inv (E.ι A 1)) (E.ι A 1) =
      E.comp (E.inv (E.ι A 1)) (E.comp (E.ι A 1) (E.ι A 1)) := by rw [← h]
  rw [E.inv_comp, cancel2] at h2
  exact h2.symm

lemma P_iota (A : G) (k : K A) : E.P (E.ι A k) = 𝟙 A := (E.ι_range A _).mpr ⟨k, rfl⟩

lemma P_inv_comp {A B : G} (e : E.Hom A B) : E.P (E.inv e) ≫ E.P e = 𝟙 B := by
  rw [← E.P_comp, E.comp_inv, E.P_id]

end Aux_GS215

open GroupoidSchreier.Interpretation in
theorem solution {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) :
    (∃ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s) ∧
      ∀ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s →
        ∃ F : WeakAction G K, FiberVia E s F := by
  constructor
  · refine ⟨fun A B u => E.comp (Classical.choose (E.P_surj u))
      (E.inv (Classical.choose (E.P_surj (𝟙 A)))), ?_, ?_⟩
    · intro A B u
      simp only
      rw [E.P_comp, Classical.choose_spec (E.P_surj u)]
      have h := Aux_GS215.P_inv_comp E (Classical.choose (E.P_surj (𝟙 A)))
      rw [Classical.choose_spec (E.P_surj (𝟙 A)), Category.comp_id] at h
      rw [h, Category.id_comp]
    · intro A
      exact E.comp_inv _
  · intro s hs
    obtain ⟨hsP, hs1⟩ := hs
    -- conjugation lands in the fibre
    have hconj : ∀ {A B : G} (u : A ⟶ B) (k : K A),
        E.P (E.comp (s u) (E.comp (E.ι A k) (E.inv (s u)))) = 𝟙 B := by
      intro A B u k
      rw [E.P_comp, E.P_comp, Aux_GS215.P_iota, Category.comp_id]
      exact Aux_GS215.P_inv_comp E (s u)
    have hsig : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C),
        E.P (E.comp (s v) (E.comp (s u) (E.inv (s (u ≫ v))))) = 𝟙 C := by
      intro A B C u v
      rw [E.P_comp, E.P_comp, hsP, hsP, Category.assoc]
      have := Aux_GS215.P_inv_comp E (s (u ≫ v))
      rw [hsP] at this
      exact this
    let Fm : ∀ {A B : G}, (A ⟶ B) → K A → K B := fun {A B} u k =>
      Classical.choose ((E.ι_range B _).mp (hconj u k))
    have hFm : ∀ {A B : G} (u : A ⟶ B) (k : K A),
        E.ι B (Fm u k) = E.comp (s u) (E.comp (E.ι A k) (E.inv (s u))) := fun {A B} u k =>
      Classical.choose_spec ((E.ι_range B _).mp (hconj u k))
    let σm : ∀ {A B C : G}, (A ⟶ B) → (B ⟶ C) → K C := fun {A B C} u v =>
      Classical.choose ((E.ι_range C _).mp (hsig u v))
    have hσm : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C),
        E.ι C (σm u v) = E.comp (s v) (E.comp (s u) (E.inv (s (u ≫ v)))) := fun {A B C} u v =>
      Classical.choose_spec ((E.ι_range C _).mp (hsig u v))
    have hmul : ∀ {A B : G} (u : A ⟶ B) (k₁ k₂ : K A), Fm u (k₁ * k₂) = Fm u k₁ * Fm u k₂ := by
      intro A B u k₁ k₂
      apply E.ι_injective B
      rw [E.ι_mul, hFm, hFm, hFm, E.ι_mul]
      simp only [E.assoc, Aux_GS215.cancel2]
    have hinj : ∀ {A B : G} (u : A ⟶ B), Function.Injective (Fm u) := by
      intro A B u k₁ k₂ h
      apply E.ι_injective A
      have h2 := congrArg (E.ι B) h
      rw [hFm, hFm] at h2
      have h3 := congrArg (fun X => E.comp (E.inv (s u)) (E.comp X (s u))) h2
      simp only [E.assoc, Aux_GS215.cancel2, E.inv_comp, E.comp_id] at h3
      exact h3
    have hsurj : ∀ {A B : G} (u : A ⟶ B), Function.Surjective (Fm u) := by
      intro A B u k'
      have hP : E.P (E.comp (E.inv (s u)) (E.comp (E.ι B k') (s u))) = 𝟙 A := by
        rw [E.P_comp, E.P_comp, Aux_GS215.P_iota, Category.comp_id, hsP]
        have := E.P_comp (E.inv (s u)) (s u)
        rw [E.inv_comp, E.P_id, hsP] at this
        exact this.symm
      obtain ⟨k, hk⟩ := (E.ι_range A _).mp hP
      refine ⟨k, E.ι_injective B ?_⟩
      rw [hFm, hk]
      simp only [E.assoc, Aux_GS215.cancel1, E.comp_inv, E.comp_id]
    let F : WeakAction G K :=
      { F := fun {A B} u => MulEquiv.ofBijective (MonoidHom.mk' (Fm u) (hmul u))
          ⟨hinj u, hsurj u⟩
        σ := fun {A B C} u v => σm u v
        map_id := by
          intro A x
          change Fm (𝟙 A) x = x
          apply E.ι_injective A
          rw [hFm, hs1, Aux_GS215.inv_id, E.id_comp, E.comp_id]
        σ_id := by
          intro A
          change σm (𝟙 A) (𝟙 A) = 1
          apply E.ι_injective A
          rw [hσm, Category.id_comp, hs1, Aux_GS215.inv_id, E.id_comp, E.id_comp,
            Aux_GS215.iota_one]
        conj := by
          intro A B C u v x
          change σm u v * Fm (u ≫ v) x = Fm v (Fm u x) * σm u v
          apply E.ι_injective C
          rw [E.ι_mul, E.ι_mul, hσm, hFm, hFm, hFm]
          simp only [E.assoc, Aux_GS215.cancel2]
        cocycle := by
          intro A B C D u v w
          change σm v w * σm u (v ≫ w) = Fm w (σm u v) * σm (u ≫ v) w
          apply E.ι_injective D
          rw [E.ι_mul, E.ι_mul, hσm, hσm, hFm, hσm, hσm, Category.assoc]
          simp only [E.assoc, Aux_GS215.cancel2] }
    refine ⟨F, fun A B u k => ?_, fun A B C u v => ?_⟩
    · exact hFm u k
    · exact hσm u v
