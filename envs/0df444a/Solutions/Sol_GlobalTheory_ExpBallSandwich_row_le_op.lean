-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.row_le_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:24.914968+00:00
-- url     : https://prove2.me/submissions/eb36c589-67ed-47b1-ba93-0ab08067b4c3

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
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
theorem _root_.solution (M : Matrix n n ℂ) (i : n) : ∑ j, ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.2 this
  simpa using h2
end GlobalTheory.ExpBallSandwich
