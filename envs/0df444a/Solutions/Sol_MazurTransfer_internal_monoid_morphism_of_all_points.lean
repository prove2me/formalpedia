-- Prove2me | solution 1 for MazurTransfer.internal_monoid_morphism_of_all_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T21:39:45.014804+00:00
-- url     : https://prove2.me/submissions/c9dc9d32-0dbb-427d-8588-c56ec9d71d2e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a morphism preserving identity and multiplication on all
test objects is an internal monoid morphism, by the fully faithful monoid
Yoneda embedding. Named downstream consumer: the actual Picard diamond
and nineteen-norm endomorphisms as internal group morphisms.
-/
import Mathlib

noncomputable section
universe u v
namespace MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw
open CategoryTheory Opposite
open scoped CategoryTheory.MonObj
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N]

theorem isMonHom_of_all_points (f : M ⟶ N)
    (h1 : ∀ T : C, (1 : T ⟶ M) ≫ f = 1)
    (hm : ∀ (T : C) (a b : T ⟶ M), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) :
    IsMonHom f := by
  let α : yonedaMonObj M ⟶ yonedaMonObj N :=
    { app T := MonCat.ofHom
        { toFun := fun a => a ≫ f
          map_one' := h1 T.unop
          map_mul' := hm T.unop }
      naturality := by
        intro T T' k
        apply MonCat.hom_ext
        apply MonoidHom.ext
        intro a
        exact Category.assoc k.unop a f }
  let g : Mon.mk M ⟶ Mon.mk N := yonedaMonFullyFaithful.preimage α
  have hg : g.hom = f := by
    change (𝟙 M) ≫ f = f
    exact Category.id_comp f
  exact hg ▸ g.isMonHom_hom

end MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw
#print axioms MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points

open CategoryTheory
open scoped CategoryTheory.MonObj
theorem solution {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : ∀ T : C, (1 : T ⟶ M) ≫ f = 1)
    (hm : ∀ (T : C) (a b : T ⟶ M), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f :=
  MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points f h1 hm

#print axioms solution
