-- Prove2me | solution 1 for GlobalTheory.T.columnGramDeterminant_unitLower_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:56.985537+00:00
-- url     : https://prove2.me/submissions/9b6bf02e-d205-45cd-a538-61a6afcedbf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThreeStatement
import Theorems.Thm_GlobalTheory_IntBall_colGram_three_unitLower


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
theorem _root_.solution : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  first | exact @GlobalTheory.IntBall.colGram_three_unitLower | exact GlobalTheory.IntBall.colGram_three_unitLower | (intros; apply GlobalTheory.IntBall.colGram_three_unitLower <;> assumption)
end _root_.GlobalTheory.T
