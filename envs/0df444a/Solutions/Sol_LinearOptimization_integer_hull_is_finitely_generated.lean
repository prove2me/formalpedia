-- Prove2me | solution 1 for LinearOptimization.integer_hull_is_finitely_generated
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T03:24:30.477375+00:00
-- url     : https://prove2.me/submissions/69d18ff9-908c-4633-9183-5a68f89fc9a9

import Theorems.Thm_LinearOptimization_integer_polyhedron_points_natGenerated
import Theorems.Thm_LinearOptimization_convexHull_natGenerated_eq_finitelyGeneratedSet

open Matrix

/-- Bertsimas--Tsitsiklis, Theorem 11.3, p. 496, using the finite integer
generation and convexification steps in Exercise 11.8(c)--(d), p. 525. -/
theorem solution {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ)
    (hfeas : (LinearOptimization.polyhedron
      (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))).Nonempty) :
    LinearOptimization.IsFinitelyGenerated
      (convexHull ℝ
        (LinearOptimization.lagrangeanIntegerSet
          (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)))) := by
  obtain ⟨k, r, x, w, hX⟩ :=
    LinearOptimization.integer_polyhedron_points_natGenerated D d
  refine ⟨k, r, x, w, ?_⟩
  rw [hX]
  exact LinearOptimization.convexHull_natGenerated_eq_finitelyGeneratedSet x w
