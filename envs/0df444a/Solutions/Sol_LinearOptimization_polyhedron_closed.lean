-- Prove2me | solution 1 for LinearOptimization.polyhedron_closed
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:42:27.257155+00:00
-- url     : https://prove2.me/submissions/c07ab102-60b7-46c1-871b-0aa6e293380f

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_Polyhedron

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    IsClosed (LinearOptimization.polyhedron A b) := by
  rw [show LinearOptimization.polyhedron A b =
      ⋂ i : Fin m, {x : Fin n → ℝ | b i ≤ A.mulVec x i} by
    ext x
    simp only [LinearOptimization.polyhedron, Set.mem_setOf_eq,
      Set.mem_iInter, Pi.le_def]]
  apply isClosed_iInter
  intro i
  apply isClosed_le continuous_const
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)
