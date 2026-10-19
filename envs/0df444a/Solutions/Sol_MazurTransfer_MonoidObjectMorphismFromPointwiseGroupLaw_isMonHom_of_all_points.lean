-- Prove2me | solution 1 for MazurTransfer.MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T08:23:17.044988+00:00
-- url     : https://prove2.me/submissions/7ff24942-32c7-4d5c-99af-34e4d8d8e53f

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
open CategoryTheory Opposite
open scoped CategoryTheory.MonObj
theorem solution {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
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
#print axioms solution
