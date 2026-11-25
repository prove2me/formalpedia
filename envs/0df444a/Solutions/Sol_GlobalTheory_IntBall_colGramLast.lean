-- Prove2me | solution 1 for GlobalTheory.IntBall.colGramLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:45.5918+00:00
-- url     : https://prove2.me/submissions/0ee946bf-56d7-4df1-95de-b7f5cc8f0656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerBlockLastEqOne
import Theorems.Thm_GlobalTheory_IntBall_colGram_blkW_last

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
open GlobalTheory GlobalTheory.IntBall
namespace GlobalTheory.IntBall
theorem _root_.solution : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last
end GlobalTheory.IntBall
