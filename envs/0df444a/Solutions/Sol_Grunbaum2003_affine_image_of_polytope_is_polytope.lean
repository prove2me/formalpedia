-- Prove2me | solution 1 for Grunbaum2003.affine_image_of_polytope_is_polytope
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:00:28.77213+00:00
-- url     : https://prove2.me/submissions/0ddf7288-e7dd-47a5-a45e-af4f466dd1fc

import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

theorem solution :
    ∀ (d j : ℕ) (V : Set (Fin d → ℝ)), V.Finite →
      ∀ f : (Fin d → ℝ) →ₗ[ℝ] (Fin j → ℝ),
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' (convexHull ℝ V) = convexHull ℝ W := by
  intro d j V hV f
  exact ⟨f '' V, hV.image f, f.image_convexHull V⟩
