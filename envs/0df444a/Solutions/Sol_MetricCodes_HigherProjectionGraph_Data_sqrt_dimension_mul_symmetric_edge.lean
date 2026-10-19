-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.sqrt_dimension_mul_symmetric_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/f21f6fa2-9a33-4b7e-922f-5553c9a5f87a

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
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.HigherProjectionGraph
variable {I X : Type*} [Fintype I] [DecidableEq I]
open MetricCodes.HigherProjectionGraph.Data
variable {D d Q : ℕ} (A : Data I X D d Q)
namespace MetricCodes.HigherProjectionGraph.Data
theorem _root_.solution (target source : I) :
    Real.sqrt (A.dimension source : ℝ) *
        Real.sqrt
          (A.probability source target * A.probability target source) =
      A.probability target source * Real.sqrt (A.dimension target : ℝ) := by
  have hs : 0 ≤ (A.dimension source : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ (A.dimension target : ℝ) := Nat.cast_nonneg _
  have hpst := A.probability_nonneg source target
  have hpts := A.probability_nonneg target source
  have hsquare :
      (Real.sqrt (A.dimension source : ℝ) *
        Real.sqrt
          (A.probability source target * A.probability target source)) ^ 2 =
      (A.probability target source *
        Real.sqrt (A.dimension target : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs,
      Real.sq_sqrt (mul_nonneg hpst hpts),
      mul_pow, Real.sq_sqrt ht]
    have hb := A.balance target source
    nlinarith
  nlinarith [Real.sqrt_nonneg (A.dimension source : ℝ),
    Real.sqrt_nonneg
      (A.probability source target * A.probability target source),
    Real.sqrt_nonneg (A.dimension target : ℝ),
    mul_nonneg hpts (Real.sqrt_nonneg (A.dimension target : ℝ)),
    mul_nonneg (Real.sqrt_nonneg (A.dimension source : ℝ))
      (Real.sqrt_nonneg
        (A.probability source target * A.probability target source))]
end MetricCodes.HigherProjectionGraph.Data
