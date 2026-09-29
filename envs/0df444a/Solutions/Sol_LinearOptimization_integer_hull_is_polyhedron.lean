-- Prove2me | solution 1 for LinearOptimization.integer_hull_is_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T03:05:34.513623+00:00
-- url     : https://prove2.me/submissions/744c0aca-86e0-43fa-9056-78f354b08992

import Theorems.Thm_LinearOptimization_integer_hull_is_finitely_generated
import Theorems.Thm_LinearOptimization_finitely_generated_is_polyhedron

open Matrix
open LinearOptimization

/-- Bertsimas--Tsitsiklis, Theorem 11.3, p. 496, with its finite-generation
core isolated exactly as outlined in Exercise 11.8, p. 525. -/
theorem solution {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ)
    (hfeas : (polyhedron (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))).Nonempty) :
    ∃ (k : ℕ) (F : Matrix (Fin k) (Fin n) ℝ) (f : Fin k → ℝ),
      convexHull ℝ
          (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) =
        polyhedron F f := by
  rcases integer_hull_is_finitely_generated D d hfeas with ⟨k, r, x, w, hfg⟩
  rcases finitely_generated_is_polyhedron x w with ⟨m', F, f, hpoly⟩
  exact ⟨m', F, f, hfg.trans hpoly⟩
