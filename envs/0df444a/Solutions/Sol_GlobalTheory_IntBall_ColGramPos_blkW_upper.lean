-- Prove2me | solution 1 for GlobalTheory.IntBall.ColGramPos.blkW_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:30.099017+00:00
-- url     : https://prove2.me/submissions/2d0a68c3-32ef-4de9-bcbc-81e504f57446

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
theorem _root_.solution {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i j : Fin (r - 1)) (h : i < j) :
    blkW p0 w i j = 0 := by
  have h' : (i : ℕ) < j := h
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
end GlobalTheory.IntBall.ColGramPos
