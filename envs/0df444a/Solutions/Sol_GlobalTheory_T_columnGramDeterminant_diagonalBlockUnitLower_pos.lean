-- Prove2me | solution 1 for GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:50.490424+00:00
-- url     : https://prove2.me/submissions/4a32f1d1-2598-4f17-bdf0-b67190dfa2ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPosStatement
import Theorems.Thm_GlobalTheory_IntBall_ColGramPos_colGram_blkW_pos


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
theorem _root_.solution : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  first | exact @GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | exact GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | (intros; apply GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos <;> assumption)
end _root_.GlobalTheory.T
