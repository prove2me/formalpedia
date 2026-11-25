-- Prove2me | solution 1 for GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:47.987627+00:00
-- url     : https://prove2.me/submissions/f14670fc-9171-4556-a8a8-09196b31a8af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerBlockLastEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerBlockLastEqOneStatement
import Theorems.Thm_GlobalTheory_IntBall_colGramLast


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
theorem _root_.solution : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  first | exact @GlobalTheory.IntBall.colGramLast | exact GlobalTheory.IntBall.colGramLast | (intros; apply GlobalTheory.IntBall.colGramLast <;> assumption)
end _root_.GlobalTheory.T
