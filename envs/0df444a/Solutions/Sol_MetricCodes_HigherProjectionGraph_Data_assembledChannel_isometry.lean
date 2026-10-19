-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.assembledChannel_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/e1bcf989-0bde-478d-9412-6044608eec48

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_edgeCoefficient_sq_sum
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_edgeCoefficient_smul_channelGram

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
theorem _root_.solution [Nonempty I] :
    (A.assembledChannel)ᵀ * A.assembledChannel =
      (1 : Matrix (Fin D) (Fin D) ℝ) := by
  classical
  unfold assembledChannel
  rw [weighted_matrix_transpose_mul_metriccodes2_81758290]
  have hcross (e f : I × I) :
      (A.channel e.1 e.2)ᵀ * A.channel f.1 f.2 =
        if e = f then
          if 0 < A.probability e.1 e.2 then A.block e.2 else 0
        else 0 := by
    by_cases hef : e = f
    · subst f
      simp [A.channel_isometry]
    · simp [hef,
        A.channel_orthogonal e.1 e.2 f.1 f.2
          (by simpa using hef)]
  simp_rw [hcross]
  simp only [smul_ite, smul_zero]
  simp only [Fintype.sum_ite_eq]
  have hedge (target source : I) :
      (if 0 < A.probability target source then
        (A.edgeCoefficient target source ^ 2) • A.block source
      else 0) =
        (A.edgeCoefficient target source ^ 2) • A.block source := by
    simpa [smul_ite] using
      A.edgeCoefficient_smul_channelGram target source
  simp_rw [← pow_two, hedge]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ source, ∑ target,
      A.edgeCoefficient target source ^ 2 • A.block source) =
        ∑ source,
          (∑ target, A.edgeCoefficient target source ^ 2) •
            A.block source := by
              simp_rw [Finset.sum_smul]
    _ = ∑ source, A.block source := by
          simp_rw [A.edgeCoefficient_sq_sum, one_smul]
    _ = 1 := A.block_complete
end MetricCodes.HigherProjectionGraph.Data
