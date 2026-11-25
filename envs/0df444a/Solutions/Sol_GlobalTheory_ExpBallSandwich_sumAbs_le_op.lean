-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.sumAbs_le_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:44.413061+00:00
-- url     : https://prove2.me/submissions/565eb552-3e26-4a30-869b-8fe13e37c5d3

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Theorems.Thm_GlobalTheory_ExpBallSandwich_row_le_op
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
theorem _root_.solution (M : Matrix n n ℂ) : sumAbs M ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  unfold sumAbs
  calc _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => row_le_op M i
    _ = _ := by simp
end GlobalTheory.ExpBallSandwich
