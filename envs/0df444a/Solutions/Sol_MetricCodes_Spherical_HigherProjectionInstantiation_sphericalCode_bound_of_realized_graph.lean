-- Prove2me | solution 1 for MetricCodes.Spherical.HigherProjectionInstantiation.sphericalCode_bound_of_realized_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/47f77cab-d98b-4a94-91fc-579d7d3dd1d1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_code_bound
import Theorems.Thm_MetricCodes_Spherical_HigherProjectionInstantiation_mem_codePoints_iff

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
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherProjectionInstantiation
theorem _root_.solution
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {n D d Q : ℕ}
    (A : MetricCodes.HigherProjectionGraph.Data
      I (SpherePoint n) D d Q)
    (hinner : ∀ x y : SpherePoint n,
      A.correlation x y =
        ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ)
    {s : ℝ} (hd : 0 < d) (hs : s < 1)
    (hgap : s < A.eigenvalue)
    (C : SpherePacking.SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (A.eigenvalue - s)) *
        ((∑ i, (A.dimension i : ℝ)) / (d : ℝ)) := by
  have h := A.code_bound (codePoints C) hd hs hgap
    (fun x _ => by
      rw [hinner]
      simp [x.property])
    (fun x hx y hy hxy => by
      rw [hinner]
      apply C.inner_le x.val ((mem_codePoints_iff C x).mp hx)
        y.val ((mem_codePoints_iff C y).mp hy)
      intro h
      apply hxy
      exact Subtype.ext h)
  simpa only [codePoints_card] using h
end MetricCodes.Spherical.HigherProjectionInstantiation
