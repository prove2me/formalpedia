-- Prove2me | solution 1 for Grunbaum2003.affineMap_image_of_polytope_is_polytope
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-08T21:38:49.630819+00:00
-- url     : https://prove2.me/submissions/cab0ccdb-7f6a-4d84-a396-bf0e886cab68

import Mathlib

set_option autoImplicit false

-- Grunbaum2003.affineMap_image_of_polytope_is_polytope
--
-- IMPORTANT (2026-10-09): the published formal statement's arrow `→ₐ[ℝ]` uses
-- U+2090 (LATIN SUBSCRIPT SMALL LETTER A), which in this Mathlib revision is
-- notation for `AlgHom R A B` (algebra homomorphisms), NOT the affine-map
-- arrow. So the node as published quantifies over algebra homs. The statement
-- remains true: every AlgHom is linear, so we reduce to
-- `LinearMap.image_convexHull` via `AlgHom.toLinearMap`, and finiteness via
-- `Set.Finite.image`. The U+2090 arrow is kept verbatim to match the node's
-- formal statement byte-for-byte.

theorem solution :
    ∀ (d j : ℕ) (V : Set (Fin d → ℝ)), V.Finite →
      ∀ f : (Fin d → ℝ) →ₐ[ℝ] (Fin j → ℝ),
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' (convexHull ℝ V) = convexHull ℝ W := by
  intro d j V hV f
  exact ⟨f '' V, hV.image ⇑f, f.toLinearMap.image_convexHull V⟩

theorem Grunbaum2003.affineMap_image_of_polytope_is_polytope :
    ∀ (d j : ℕ) (V : Set (Fin d → ℝ)), V.Finite →
      ∀ f : (Fin d → ℝ) →ₐ[ℝ] (Fin j → ℝ),
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' (convexHull ℝ V) = convexHull ℝ W :=
  solution
