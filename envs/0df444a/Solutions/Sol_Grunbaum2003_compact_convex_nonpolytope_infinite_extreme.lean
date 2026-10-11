-- Prove2me | solution 1 for Grunbaum2003.compact_convex_nonpolytope_infinite_extreme
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-11T04:04:11.915371+00:00
-- url     : https://prove2.me/submissions/82cfbcee-7209-4f0a-bead-02e5f92c420e

import Mathlib

set_option autoImplicit false

/-- Lemma B (Krein–Milman step): a compact convex K that is not a finite hull
    has infinitely many extreme points. By contradiction: finitely many extreme
    points would make K = closure (hull (extreme)) = hull (extreme), a finite hull. -/
theorem solution (d : ℕ)
    (K : Set (Fin d → ℝ)) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (hnotpoly : ¬ ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) :
    (K.extremePoints ℝ).Infinite := by
  by_contra h
  rw [Set.not_infinite] at h
  have hclosed : IsClosed (convexHull ℝ (K.extremePoints ℝ)) :=
    (h.isCompact_convexHull ℝ).isClosed
  have hkm := closure_convexHull_extremePoints hcompact hconvex
  rw [hclosed.closure_eq] at hkm
  exact hnotpoly ⟨K.extremePoints ℝ, h, hkm.symm⟩

theorem Grunbaum2003.compact_convex_nonpolytope_infinite_extreme :
    ∀ (d : ℕ) (K : Set (Fin d → ℝ)) (hcompact : IsCompact K)
      (hconvex : Convex ℝ K)
      (hnotpoly : ¬ ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V),
      (K.extremePoints ℝ).Infinite := solution
