-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.sumAbs_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:27.630481+00:00
-- url     : https://prove2.me/submissions/f81095a0-90cc-4c70-b75f-efe069824847

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
omit [DecidableEq n]
namespace GlobalTheory.ExpBallSandwich
theorem _root_.solution (A : Matrix n n ℂ) : sumAbs (-A) = sumAbs A := by
  simp [sumAbs]
end GlobalTheory.ExpBallSandwich
