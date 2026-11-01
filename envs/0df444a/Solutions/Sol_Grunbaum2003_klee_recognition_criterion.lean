-- Prove2me | solution 1 for Grunbaum2003.klee_recognition_criterion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T17:57:17.105575+00:00
-- url     : https://prove2.me/submissions/0ab01f1a-6d72-4753-9edb-754147009b53

import Theorems.Thm_Grunbaum2003_projections_polytope_implies_closed
import Theorems.Thm_Grunbaum2003_compact_convex_nonpolytope_infinite_extreme
import Theorems.Thm_Grunbaum2003_generic_projection_nonpolytope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K)
    (hproj : ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
      ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W) :
    ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V := by
  have hclosed : IsClosed K :=
    projections_polytope_implies_closed d hd K hbounded hconvex hproj
  have hcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  by_contra hnotpoly
  have hext : (K.extremePoints ℝ).Infinite :=
    compact_convex_nonpolytope_infinite_extreme d K hcompact hconvex hnotpoly
  obtain ⟨j, hj2, hjd, hproj_j⟩ := hproj
  obtain ⟨f, hsurj, hnotW⟩ :=
    generic_projection_nonpolytope d hd K hcompact hconvex hext j hj2 hjd
  exact hnotW (hproj_j f hsurj)
