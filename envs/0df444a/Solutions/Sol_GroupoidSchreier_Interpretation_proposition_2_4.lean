-- Prove2me | solution 1 for GroupoidSchreier.Interpretation.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:39:35.754768+00:00
-- url     : https://prove2.me/submissions/3ecd6f42-1eb0-4c20-bfd4-883b1687fff0

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction

open CategoryTheory
universe u

open GroupoidSchreier.Interpretation in
theorem solution {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) {A B : G} (u : A ⟶ B) :
    F.σ (𝟙 A) u = 1 ∧ F.σ u (𝟙 B) = 1 := by
  constructor
  · have h := F.cocycle (𝟙 A) (𝟙 A) u
    simp only [Category.id_comp] at h
    rw [F.σ_id, map_one, one_mul] at h
    exact mul_eq_right.mp h
  · have h := F.cocycle u (𝟙 B) (𝟙 B)
    simp only [Category.comp_id] at h
    rw [F.σ_id, F.map_id, one_mul] at h
    exact (mul_eq_left.mp h.symm)
