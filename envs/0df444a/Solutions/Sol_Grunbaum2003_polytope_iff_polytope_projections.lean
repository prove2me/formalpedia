-- Prove2me | solution 1 for Grunbaum2003.polytope_iff_polytope_projections
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T17:57:17.765959+00:00
-- url     : https://prove2.me/submissions/1786042a-aea1-47d0-88a2-a61e7d924b59

import Theorems.Thm_Grunbaum2003_klee_recognition_criterion
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K) :
    (∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) ↔
      ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
        ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
          ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W := by
  constructor
  · rintro ⟨V, hV, rfl⟩
    refine ⟨2, le_rfl, hd, fun f _ => ⟨f '' V, hV.image f, f.image_convexHull V⟩⟩
  · intro hproj
    exact klee_recognition_criterion d hd K hbounded hconvex hproj
