-- Prove2me | solution 1 for LinearOptimization.polyhedron_bounded_convex_hull_extreme
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:34:57.627393+00:00
-- url     : https://prove2.me/submissions/b9ad7b6a-5ece-4d3d-ad7b-f34cdb07f3a0

import Theorems.Thm_LinearOptimization_polyhedron_closed
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

open Matrix

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (LinearOptimization.polyhedron A b).Nonempty)
    (hbd : LinearOptimization.IsBoundedSet (LinearOptimization.polyhedron A b)) :
    LinearOptimization.polyhedron A b =
      convexHull ℝ (Set.extremePoints ℝ (LinearOptimization.polyhedron A b)) := by
  classical
  let C := LinearOptimization.generalFormSystem A b
  have hCset : LinearOptimization.constraintSet C = LinearOptimization.polyhedron A b := by
    ext y
    constructor
    · intro hy i
      simpa [C, LinearOptimization.generalFormSystem,
        LinearOptimization.LinearConstraint.IsSatisfiedAt, Matrix.mulVec_apply_eq_sum, dotProduct] using hy i
    · intro hy i
      simpa [C, LinearOptimization.generalFormSystem,
        LinearOptimization.LinearConstraint.IsSatisfiedAt, Matrix.mulVec_apply_eq_sum, dotProduct] using hy i
  have hneC : (LinearOptimization.constraintSet C).Nonempty := by
    simpa [hCset] using hne
  have hext_eq : Set.extremePoints ℝ (LinearOptimization.polyhedron A b) =
      {y | LinearOptimization.IsBasicFeasibleSolution C y} := by
    ext y
    constructor
    · intro hy
      have hymem : y ∈ LinearOptimization.constraintSet C := by
        rw [hCset]
        exact hy.1
      have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv C y hneC hymem
      apply (ht.out 1 2).mp
      rw [hCset]
      exact hy
    · intro hy
      have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv C y hneC hy.2
      have hextC := (ht.out 2 1).mp hy
      rw [hCset] at hextC
      exact hextC
  have hextFinite :
      (Set.extremePoints ℝ (LinearOptimization.polyhedron A b)).Finite := by
    rw [hext_eq]
    exact (LinearOptimization.lp_basic_solutions_finite C).2
  have hconvex : Convex ℝ (LinearOptimization.polyhedron A b) := by
    intro x hx y hy r s hr hs hsum
    intro i
    have hxi : b i ≤ A i ⬝ᵥ x := hx i
    have hyi : b i ≤ A i ⬝ᵥ y := hy i
    change b i ≤ A i ⬝ᵥ (r • x + s • y)
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hxmul : r * b i ≤ r * (A i ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_left hxi hr
    have hymul : s * b i ≤ s * (A i ⬝ᵥ y) :=
      mul_le_mul_of_nonneg_left hyi hs
    calc
      b i = r * b i + s * b i := by rw [← add_mul, hsum, one_mul]
      _ ≤ r * (A i ⬝ᵥ x) + s * (A i ⬝ᵥ y) := add_le_add hxmul hymul
  obtain ⟨K, hK⟩ := hbd
  let K' := max 0 K
  have hKnonneg : 0 ≤ K' := le_max_left _ _
  have hnorm : ∀ y ∈ LinearOptimization.polyhedron A b, ‖y‖ ≤ K' := by
    intro y hy
    apply (pi_norm_le_iff_of_nonneg hKnonneg).2
    intro i
    have hi := hK y hy i
    calc
      ‖y i‖ = |y i| := Real.norm_eq_abs _
      _ ≤ K := hi
      _ ≤ K' := le_max_right _ _
  have hbounded := (Metric.isBounded_iff
    (α := Fin n → ℝ) (s := LinearOptimization.polyhedron A b)).2 ⟨2 * K', by
    intro x hx y hy
    rw [dist_eq_norm]
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ K' + K' := add_le_add (hnorm x hx) (hnorm y hy)
      _ = 2 * K' := by ring⟩
  have hcompact : IsCompact (LinearOptimization.polyhedron A b) :=
    Metric.isCompact_iff_isClosed_bounded.2
      ⟨LinearOptimization.polyhedron_closed A b, hbounded⟩
  have hKM := closure_convexHull_extremePoints hcompact hconvex
  have hclosedHull := hextFinite.isClosed_convexHull ℝ
  rw [hclosedHull.closure_eq] at hKM
  exact hKM.symm
