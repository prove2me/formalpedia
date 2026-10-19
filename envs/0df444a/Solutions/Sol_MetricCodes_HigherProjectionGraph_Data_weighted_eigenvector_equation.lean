-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.weighted_eigenvector_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/a766d84c-9ec6-4f79-b260-b772b0129604

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_sqrt_dimension_mul_symmetric_edge

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
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.HigherProjectionGraph
variable {I X : Type*} [Fintype I] [DecidableEq I]
open MetricCodes.HigherProjectionGraph.Data
variable {D d Q : ℕ} (A : Data I X D d Q)
namespace MetricCodes.HigherProjectionGraph.Data
theorem _root_.solution (source : I) :
    (∑ target, A.probability target source * A.weight target) =
      A.eigenvalue * A.weight source := by
  calc
    (∑ target, A.probability target source * A.weight target) =
        ∑ target,
          Real.sqrt (A.dimension source : ℝ) *
            (Real.sqrt
              (A.probability source target *
                A.probability target source) * A.eigenvector target) := by
          apply Finset.sum_congr rfl
          intro target _
          change
            A.probability target source *
                (Real.sqrt (A.dimension target : ℝ) *
                  A.eigenvector target) = _
          calc
            A.probability target source *
                (Real.sqrt (A.dimension target : ℝ) *
                  A.eigenvector target) =
                (A.probability target source *
                  Real.sqrt (A.dimension target : ℝ)) *
                    A.eigenvector target := by ring
            _ = (Real.sqrt (A.dimension source : ℝ) *
                  Real.sqrt
                    (A.probability source target *
                      A.probability target source)) *
                    A.eigenvector target := by
                  rw [A.sqrt_dimension_mul_symmetric_edge target source]
            _ = _ := by ring
    _ = Real.sqrt (A.dimension source : ℝ) *
          (∑ target,
            Real.sqrt
              (A.probability source target *
                A.probability target source) * A.eigenvector target) := by
          rw [Finset.mul_sum]
    _ = A.eigenvalue * A.weight source := by
          rw [A.eigenvector_equation source]
          change
            Real.sqrt (A.dimension source : ℝ) *
                (A.eigenvalue * A.eigenvector source) =
              A.eigenvalue *
                (Real.sqrt (A.dimension source : ℝ) *
                  A.eigenvector source)
          ring
end MetricCodes.HigherProjectionGraph.Data
