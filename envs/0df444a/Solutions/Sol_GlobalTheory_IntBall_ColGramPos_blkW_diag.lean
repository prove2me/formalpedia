-- Prove2me | solution 1 for GlobalTheory.IntBall.ColGramPos.blkW_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:22.670971+00:00
-- url     : https://prove2.me/submissions/4f3fe500-f69c-4a99-a648-8acd4a28992a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos

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
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.ColGramPos
open scoped ComplexOrder
namespace GlobalTheory.IntBall.ColGramPos
theorem _root_.solution {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]
end GlobalTheory.IntBall.ColGramPos
