-- Prove2me | solution 1 for GlobalTheory.FlagGram.rpow_neg_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:47:30.737443+00:00
-- url     : https://prove2.me/submissions/40217e19-d026-4534-b8b3-1fb9a5853243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagGramDensityInequalityComplex

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
open GlobalTheory GlobalTheory.FlagGram
namespace GlobalTheory.FlagGram
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) :
    t ^ (-(4/3:ℝ)) = ((t ^ (1/3:ℝ)) ^ 4)⁻¹ := by
  rw [Real.rpow_neg ht, ← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num
end GlobalTheory.FlagGram
