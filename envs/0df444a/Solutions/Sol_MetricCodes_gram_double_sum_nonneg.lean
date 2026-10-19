-- Prove2me | solution 1 for MetricCodes.gram_double_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/fc9936c8-4d28-4f91-8d6f-f4dc4963ddbd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace MetricCodes
theorem _root_.solution (C : Finset X) (q : X → E) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
  classical
  calc
    0 ≤ ⟪∑ x ∈ C, q x, ∑ x ∈ C, q x⟫_ℝ :=
      real_inner_self_nonneg
    _ = ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]
end MetricCodes
