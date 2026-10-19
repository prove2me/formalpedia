-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.eigenvector_zero_of_positive_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/b5f6dd74-c3f2-4baa-bc8f-0eba9fbb5ad1

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
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (hzero : x i = 0) (hedge : 0 < A i j) :
    x j = 0 := by
  have hrow := congrArg (fun z : Space I => z i) heig
  change (∑ k : I, A i k * x k) = eigenvalue * x i at hrow
  rw [hzero, mul_zero] at hrow
  have hsingle : A i j * x j ≤ ∑ k : I, A i k * x k := by
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hnonneg i k) (hx k))
      (Finset.mem_univ j)
  rw [hrow] at hsingle
  have hterm : A i j * x j = 0 :=
    le_antisymm hsingle (mul_nonneg (hnonneg i j) (hx j))
  exact (mul_eq_zero.mp hterm).resolve_left hedge.ne'
end MetricCodes.Spherical.HigherHierarchyFinitePerron
