-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.assembledChannel_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/adf05b1d-43b1-44e3-9960-9f15b69cc2b8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_edgeCoefficient_axis_sum

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
theorem _root_.solution [Nonempty I] (x : X) :
    (A.assembledChannel)ᵀ * A.axis x * A.combinedFibre x =
      Real.sqrt A.eigenvalue • A.combinedFibre x := by
  classical
  unfold assembledChannel combinedFibre
  simp only [Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul]
  simp_rw [A.channel_axis]
  simp only [smul_ite, smul_zero]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [smul_ite, smul_zero]
  calc
    (∑ target, ∑ j, ∑ source,
        if target = j then
          A.amplitude j •
            (A.edgeCoefficient target source *
              Real.sqrt (A.probability target source)) •
                A.fibre source x
        else 0) =
        ∑ target, ∑ source,
          (A.amplitude target *
            (A.edgeCoefficient target source *
              Real.sqrt (A.probability target source))) •
                A.fibre source x := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          simp [smul_smul]
    _ = ∑ source,
          (Real.sqrt A.eigenvalue * A.amplitude source) •
            A.fibre source x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          rw [← Finset.sum_smul]
          congr 1
          calc
            (∑ target,
              A.amplitude target *
                (A.edgeCoefficient target source *
                  Real.sqrt (A.probability target source))) =
                ∑ target,
                  A.edgeCoefficient target source * A.amplitude target *
                    Real.sqrt (A.probability target source) := by
                    apply Finset.sum_congr rfl
                    intro target _
                    ring
            _ = _ := A.edgeCoefficient_axis_sum source
end MetricCodes.HigherProjectionGraph.Data
