-- Prove2me | solution 1 for GroupoidSchreier.Interpretation.definition_2_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:05:12.453974+00:00
-- url     : https://prove2.me/submissions/1902631e-9345-41c1-a2d3-4ce533e740f8

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

open CategoryTheory

universe u

namespace Aux_GS217
open GroupoidSchreier.Interpretation

variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] (F : WeakAction G K)

lemma σ_comp_id {A B : G} (f : A ⟶ B) : F.σ f (𝟙 B) = 1 := by
  have h := F.cocycle f (𝟙 B) (𝟙 B)
  rw [Category.comp_id, Category.comp_id, F.σ_id, one_mul, F.map_id] at h
  exact (mul_eq_left.mp h.symm)

lemma σ_id_comp {A C : G} (w : A ⟶ C) : F.σ (𝟙 A) w = 1 := by
  have h := F.cocycle (𝟙 A) (𝟙 A) w
  rw [Category.id_comp, Category.id_comp, F.σ_id, map_one, one_mul] at h
  exact mul_eq_right.mp h

lemma σ_inv {A B : G} (f : A ⟶ B) :
    F.σ (Groupoid.inv f) f = F.F f (F.σ f (Groupoid.inv f)) := by
  have h := F.cocycle f (Groupoid.inv f) f
  rw [Groupoid.inv_comp, Groupoid.comp_inv, σ_comp_id, σ_id_comp, mul_one, mul_one] at h
  exact h

lemma FF_inv {A B : G} (f : A ⟶ B) (k : K B) :
    F.F f (F.F (Groupoid.inv f) k) =
      F.σ (Groupoid.inv f) f * k * (F.σ (Groupoid.inv f) f)⁻¹ := by
  have h := F.conj (Groupoid.inv f) f k
  rw [Groupoid.inv_comp, F.map_id] at h
  rw [eq_mul_inv_iff_mul_eq, ← h]

end Aux_GS217

open GroupoidSchreier.Interpretation in
theorem solution {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) :
    ∃ (E : Extension G K) (φ : ∀ A B : G, E.Hom A B ≃ (A ⟶ B) × K B),
      (∀ (A B C : G) (g : E.Hom B C) (f : E.Hom A B),
        φ A C (E.comp g f) = twistedComp F (φ B C g) (φ A B f)) ∧
      (∀ A : G, φ A A (E.id A) = (𝟙 A, 1)) ∧
      (∀ (A B : G) (e : E.Hom A B), E.P e = (φ A B e).1) ∧
      (∀ (A : G) (k : K A), φ A A (E.ι A k) = (𝟙 A, k)) ∧
      FiberVia E (fun ⦃A B : G⦄ (u : A ⟶ B) => (φ A B).symm (u, 1)) F := by
  let invH : ∀ {A B : G}, ((A ⟶ B) × K B) → ((B ⟶ A) × K A) := fun {A B} e =>
    (Groupoid.inv e.1, (F.F (Groupoid.inv e.1) e.2 * F.σ e.1 (Groupoid.inv e.1))⁻¹)
  let E : Extension G K :=
    { Hom := fun A B => (A ⟶ B) × K B
      id := fun A => (𝟙 A, 1)
      comp := fun {A B C} g f => twistedComp F g f
      inv := fun {A B} e => invH e
      id_comp := by
        intro A B f
        simp only [twistedComp, Category.comp_id, F.map_id, one_mul, Aux_GS217.σ_comp_id,
          mul_one]
      comp_id := by
        intro A B f
        simp only [twistedComp, Category.id_comp, map_one, mul_one, Aux_GS217.σ_id_comp]
      assoc := by
        intro A B C D h g f
        simp only [twistedComp, Category.assoc, Prod.mk.injEq, true_and]
        rw [map_mul, map_mul]
        have c1 := F.conj g.1 h.1 f.2
        have c2 := F.cocycle f.1 g.1 h.1
        calc h.2 * (F.F h.1) g.2 * F.σ g.1 h.1 * (F.F (g.1 ≫ h.1)) f.2 * F.σ f.1 (g.1 ≫ h.1)
            = h.2 * (F.F h.1) g.2 * (F.σ g.1 h.1 * (F.F (g.1 ≫ h.1)) f.2) *
                F.σ f.1 (g.1 ≫ h.1) := by group
          _ = h.2 * (F.F h.1) g.2 * ((F.F h.1) ((F.F g.1) f.2) * F.σ g.1 h.1) *
                F.σ f.1 (g.1 ≫ h.1) := by rw [c1]
          _ = h.2 * (F.F h.1) g.2 * (F.F h.1) ((F.F g.1) f.2) *
                (F.σ g.1 h.1 * F.σ f.1 (g.1 ≫ h.1)) := by group
          _ = h.2 * (F.F h.1) g.2 * (F.F h.1) ((F.F g.1) f.2) *
                ((F.F h.1) (F.σ f.1 g.1) * F.σ (f.1 ≫ g.1) h.1) := by rw [c2]
          _ = _ := by group
      inv_comp := by
        intro A B e
        simp only [twistedComp, invH, Groupoid.comp_inv, Prod.mk.injEq, true_and]
        group
      comp_inv := by
        intro A B e
        simp only [twistedComp, invH, Groupoid.inv_comp, Prod.mk.injEq, true_and]
        rw [map_inv, map_mul, Aux_GS217.FF_inv, ← Aux_GS217.σ_inv]
        group
      P := fun {A B} e => e.1
      P_id := fun A => rfl
      P_comp := fun g f => rfl
      P_surj := fun u => ⟨(u, 1), rfl⟩
      ι := fun A k => (𝟙 A, k)
      ι_mul := by
        intro A x y
        simp only [twistedComp, Category.comp_id, F.map_id, F.σ_id, mul_one]
      ι_injective := fun A x y h => (Prod.mk.inj h).2
      ι_range := by
        intro A e
        constructor
        · intro h
          exact ⟨e.2, Prod.ext h.symm rfl⟩
        · rintro ⟨k, rfl⟩
          rfl }
  refine ⟨E, fun A B => Equiv.refl _, fun A B C g f => rfl, fun A => rfl, fun A B e => rfl,
    fun A k => rfl, ?_, ?_⟩
  · intro A B u k
    change ((𝟙 B, F.F u k) : (B ⟶ B) × K B) =
      twistedComp F (u, 1) (twistedComp F (𝟙 A, k) (invH (u, 1)))
    simp only [twistedComp, invH, Category.comp_id, Groupoid.inv_comp, map_one, one_mul,
      F.map_id, Aux_GS217.σ_comp_id, mul_one, Prod.mk.injEq, true_and]
    rw [map_mul, map_inv, ← Aux_GS217.σ_inv]
    group
  · intro A B C u v
    change ((𝟙 C, F.σ u v) : (C ⟶ C) × K C) =
      twistedComp F (v, 1) (twistedComp F (u, 1) (invH (u ≫ v, 1)))
    simp only [twistedComp, invH, map_one, one_mul, Prod.mk.injEq]
    refine ⟨by simp [Category.assoc, Groupoid.inv_comp], ?_⟩
    set w := u ≫ v with hw
    have c1 := F.cocycle (Groupoid.inv w) u v
    rw [← hw, Aux_GS217.σ_inv] at c1
    have c2 := F.conj u v (F.σ w (Groupoid.inv w))
    rw [← hw] at c2
    rw [map_mul, map_inv, map_inv]
    calc F.σ u v
        = ((F.F v) ((F.F u) (F.σ w (Groupoid.inv w))))⁻¹ *
            (F.σ u v * (F.F w) (F.σ w (Groupoid.inv w))) := by rw [c2]; group
      _ = ((F.F v) ((F.F u) (F.σ w (Groupoid.inv w))))⁻¹ *
            ((F.F v) (F.σ (Groupoid.inv w) u) * F.σ (Groupoid.inv w ≫ u) v) := by rw [c1]
      _ = _ := by group
