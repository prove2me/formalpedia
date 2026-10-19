-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.inner_le_inner_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/1c3fa8e7-ed57-449e-a770-424f9bc2bac5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution (A : Matrix I I ℝ)
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    @inner ℝ (Space I) _ (operator A x) x ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : I, (∑ j : I, A i j * x j) * x i) ≤
      ∑ i : I, (∑ j : I, A i j * |x j|) * |x i|
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hproduct : x j * x i ≤ |x j| * |x i| := by
    calc
      x j * x i ≤ |x j * x i| := le_abs_self _
      _ = |x j| * |x i| := abs_mul _ _
  calc
    A i j * x j * x i = A i j * (x j * x i) := by ring
    _ ≤ A i j * (|x j| * |x i|) :=
      mul_le_mul_of_nonneg_left hproduct (hA i j)
    _ = A i j * |x j| * |x i| := by ring
end MetricCodes.Spherical.HigherHierarchyFinitePerron
