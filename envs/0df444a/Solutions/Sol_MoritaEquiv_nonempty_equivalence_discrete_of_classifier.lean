-- Prove2me | solution 1 for MoritaEquiv.nonempty_equivalence_discrete_of_classifier
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T19:14:32.761862+00:00
-- url     : https://prove2.me/submissions/7d3e10bb-4d3f-49a5-b5b5-6c07ebb851bb

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv
namespace T52C

universe u v w

theorem disc_main {C : Type u} [Category.{v} C] {α : Type w} (φ : C → α)
    (hsurj : Function.Surjective φ) (hsub : ∀ X Y : C, Subsingleton (X ⟶ Y))
    (hhom : ∀ X Y : C, Nonempty (X ⟶ Y) ↔ φ X = φ Y) : Nonempty (C ≌ Discrete α) := by
  let F : C ⥤ Discrete α :=
    { obj := fun X => ⟨φ X⟩
      map := fun {X Y} f => eqToHom (congrArg Discrete.mk ((hhom X Y).1 ⟨f⟩))
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  have : F.Full := ⟨fun {X Y} g => by
    obtain ⟨f⟩ := (hhom X Y).2 (Discrete.eq_of_hom g)
    exact ⟨f, Subsingleton.elim _ _⟩⟩
  have : F.Faithful := ⟨fun {X Y} _ _ _ => by have := hsub X Y; exact Subsingleton.elim _ _⟩
  have : F.EssSurj := ⟨fun Y => by
    obtain ⟨X, hX⟩ := hsurj Y.as
    exact ⟨X, ⟨eqToIso (congrArg Discrete.mk hX)⟩⟩⟩
  have : F.IsEquivalence := { }
  exact ⟨F.asEquivalence⟩

end T52C
end MoritaEquiv

theorem solution {C : Type*} [CategoryTheory.Category C] {α : Type*}
    (φ : C → α) (hsurj : Function.Surjective φ) (hsub : ∀ X Y : C, Subsingleton (X ⟶ Y))
    (hhom : ∀ X Y : C, Nonempty (X ⟶ Y) ↔ φ X = φ Y) : Nonempty (C ≌ CategoryTheory.Discrete α) :=
  MoritaEquiv.T52C.disc_main φ hsurj hsub hhom
