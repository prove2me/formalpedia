-- Prove2me | solution 1 for GroupMetrization.struble_exists_family
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:18:08.535525+00:00
-- url     : https://prove2.me/submissions/ba6b26ac-1797-48ab-9dd6-0a0fda0fdb00

import Mathlib
import Theorems.Thm_GroupMetrization_struble

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_GroupMetrization_struble_exists_family

/-- The open balls about `1` of a proper left-invariant metric form the required family. -/
theorem family_of_metric (G : Type*) [Group G] [MetricSpace G] [ProperSpace G]
    (hinv : ∀ g x y : G, dist (g * x) (g * y) = dist x y) :
    ∃ U : ℝ → Set G,
      (∀ r : ℝ, 0 < r → IsOpen (U r) ∧ IsCompact (closure (U r)) ∧ (U r)⁻¹ = U r) ∧
      (∀ r s : ℝ, 0 < r → 0 < s → U r * U s ⊆ U (r + s)) ∧
      (𝓝 (1 : G)).HasBasis (fun r : ℝ => 0 < r) U ∧
      (⋃ r ∈ Set.Ioi (0 : ℝ), U r) = Set.univ := by
  have hsym : ∀ x : G, dist x⁻¹ 1 = dist x 1 := by
    intro x
    have := hinv x x⁻¹ 1
    rw [mul_inv_cancel, mul_one] at this
    rw [← this, dist_comm]
  refine ⟨fun r => ball 1 r, ?_, ?_, ?_, ?_⟩
  · intro r _
    refine ⟨isOpen_ball, (isCompact_closedBall (1 : G) r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, ?_⟩
    ext x
    simp only [Set.mem_inv, mem_ball]
    rw [hsym]
  · rintro r s _ _ _ ⟨x, hx, y, hy, rfl⟩
    simp only [mem_ball] at hx hy ⊢
    calc dist (x * y) 1 ≤ dist (x * y) x + dist x 1 := dist_triangle _ _ _
      _ = dist y 1 + dist x 1 := by
          have := hinv x y 1
          rw [mul_one] at this
          rw [this]
      _ < r + s := by linarith
  · exact nhds_basis_ball
  · ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi, mem_ball, Set.mem_univ, iff_true]
    exact ⟨dist x 1 + 1, by positivity, by linarith⟩

end Sol_GroupMetrization_struble_exists_family

open GroupMetrization

theorem solution (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ U : ℝ → Set G,
      (∀ r : ℝ, 0 < r → IsOpen (U r) ∧ IsCompact (closure (U r)) ∧ (U r)⁻¹ = U r) ∧
      (∀ r s : ℝ, 0 < r → 0 < s → U r * U s ⊆ U (r + s)) ∧
      (𝓝 (1 : G)).HasBasis (fun r : ℝ => 0 < r) U ∧
      (⋃ r ∈ Set.Ioi (0 : ℝ), U r) = Set.univ := by
  obtain ⟨d, hd, hinv, hcpt⟩ := (GroupMetrization.struble G).mp inferInstance
  subst hd
  exact @Sol_GroupMetrization_struble_exists_family.family_of_metric G _ d ⟨hcpt⟩ hinv
