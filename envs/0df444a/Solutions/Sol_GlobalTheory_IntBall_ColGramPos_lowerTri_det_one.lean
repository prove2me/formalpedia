-- Prove2me | solution 1 for GlobalTheory.IntBall.ColGramPos.lowerTri_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:09:30.087928+00:00
-- url     : https://prove2.me/submissions/305c0399-3122-4e54-a41f-93d166d56897

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
theorem _root_.solution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by
  rw [Matrix.det_of_lowerTriangular T (fun i j hij => hu i j hij)]
  simp [hd]
end GlobalTheory.IntBall.ColGramPos
