-- Prove2me | solution 1 for MazurTransfer.GlueDataPrimeOverlapCompatibility.glue_condition
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:20:57.901725+00:00
-- url     : https://prove2.me/submissions/44fc7987-628a-4b84-ac2c-1a9b7f8b5e0f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: remove implementation casts from the gluing condition of
a distinct-chart gluing datum. Named downstream consumer: the actual
order-13 overlap comparison, under the default proof checking limits.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.GlueDataPrimeOverlapCompatibilityHelpers20261017
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem cancel_glue_casts {U V W Z A B X : Scheme.{u}}
    (e : U ≅ V) (d : W ≅ Z) (t : V ⟶ Z) (f : Z ⟶ A) (g : V ⟶ B)
    (i : A ⟶ X) (j : B ⟶ X)
    (H : (e.hom ≫ t ≫ d.inv) ≫ (d.hom ≫ f) ≫ i = e.hom ≫ g ≫ j) :
    t ≫ f ≫ i = g ≫ j := by
  apply (cancel_epi e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using H

end MazurTransfer.GlueDataPrimeOverlapCompatibilityHelpers20261017
open MazurTransfer.GlueDataPrimeOverlapCompatibilityHelpers20261017
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
theorem solution (D : GlueData' Scheme.{u})
    [HasMulticoequalizer (GlueData.ofGlueData' D).diagram]
    (i j : D.J) (h : i ≠ j) :
    D.t i j h ≫ D.f j i h.symm ≫ (GlueData.ofGlueData' D).ι j =
      D.f i j h ≫ (GlueData.ofGlueData' D).ι i := by
  classical
  have H := (GlueData.ofGlueData' D).glue_condition i j
  have Hf : (GlueData.ofGlueData' D).f j i = eqToHom (dif_neg h.symm) ≫ D.f j i h.symm := by
    dsimp [GlueData.ofGlueData', GlueData'.f']
    simp only [dif_neg h.symm]
  have Hg : (GlueData.ofGlueData' D).f i j = eqToHom (dif_neg h) ≫ D.f i j h := by
    dsimp [GlueData.ofGlueData', GlueData'.f']
    simp only [dif_neg h]
  have Ht : (GlueData.ofGlueData' D).t i j =
      eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg h.symm).symm := by
    dsimp [GlueData.ofGlueData']
    simp only [dif_neg h]
  rw [Hf, Hg, Ht] at H
  exact cancel_glue_casts (eqToIso (dif_neg h)) (eqToIso (dif_neg h.symm))
    (D.t i j h) (D.f j i h.symm) (D.f i j h)
    ((GlueData.ofGlueData' D).ι j) ((GlueData.ofGlueData' D).ι i) H

#print axioms solution
