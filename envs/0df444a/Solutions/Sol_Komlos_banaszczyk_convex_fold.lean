-- Prove2me | solution 1 for Komlos.banaszczyk_convex_fold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:56:54.000486+00:00
-- url     : https://prove2.me/submissions/4e8f95a9-2332-4017-99e2-c39ca91dda42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Komlos_closedConvexFold_geometry
import Theorems.Thm_Komlos_closedConvexFold_gaussian_mass

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem solution (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K)
    (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ ≤ (1/5:ℝ)) :
    ∃ L : Set (EuclideanSpace ℝ (Fin m)), Convex ℝ L ∧ IsCompact L ∧
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real K ≤
        (stdGaussian (EuclideanSpace ℝ (Fin m))).real L ∧
      ∀ x ∈ L, x+u ∈ K ∨ x-u ∈ K := by
  obtain ⟨hc, hk, hs⟩ := Komlos.closedConvexFold_geometry m K hconv hcomp u
  exact ⟨Komlos.closedConvexFold m K u, hc, hk,
    Komlos.closedConvexFold_gaussian_mass m K hconv hcomp hmass u hu, hs⟩
