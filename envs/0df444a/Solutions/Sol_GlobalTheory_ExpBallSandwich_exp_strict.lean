-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.exp_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:49.29877+00:00
-- url     : https://prove2.me/submissions/f0ad6298-55c9-4be9-b9ab-faf206546ad6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_nonneg
import Theorems.Thm_GlobalTheory_ExpBallSandwich_op_le_sumAbs
import Theorems.Thm_GlobalTheory_ExpBallSandwich_sumAbs_le_op
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.ExpBallSandwich
variable {n : Type} [Fintype n] [DecidableEq n]
open scoped Matrix.Norms.Operator
namespace GlobalTheory.ExpBallSandwich
theorem _root_.solution (η : ℝ) (hη : 0 < η) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix n n ℂ,
    sumAbs A < ρ → sumAbs B < ρ →
    sumAbs (NormedSpace.exp A - NormedSpace.exp B - (A - B)) ≤ η * sumAbs (A - B) := by
  have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO
  have hc : 0 < η / ((Fintype.card n : ℝ) + 1) := by positivity
  have h2 := h.def hc
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, h3⟩ := h2
  refine ⟨ρ, hρ, fun A B hA hB => ?_⟩
  have h4 := @h3 (A, B) (by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))
  simp only [ContinuousLinearMap.one_apply] at h4
  have h5 := op_le_sumAbs (A - B)
  have h6 := sumAbs_nonneg (A - B)
  calc _ ≤ _ := sumAbs_le_op _
    _ ≤ (Fintype.card n : ℝ) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        refine mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h5 hc.le
    _ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        gcongr; linarith
    _ = _ := by field_simp
end GlobalTheory.ExpBallSandwich
