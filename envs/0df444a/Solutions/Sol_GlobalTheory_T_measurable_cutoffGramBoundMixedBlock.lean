-- Prove2me | solution 1 for GlobalTheory.T.measurable_cutoffGramBoundMixedBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:40.093605+00:00
-- url     : https://prove2.me/submissions/7580e2ce-96b0-46ff-8e46-d7b2a6f4ab57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurableCutoffGramBoundMixedBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurableCutoffGramBoundMixedBlockStatement
import Theorems.Thm_GlobalTheory_IntBall_measurable_hB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
end _root_.GlobalTheory.T
