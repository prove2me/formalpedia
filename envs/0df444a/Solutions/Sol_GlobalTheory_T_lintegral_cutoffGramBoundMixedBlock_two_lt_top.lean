-- Prove2me | solution 1 for GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:44.065541+00:00
-- url     : https://prove2.me/submissions/1c0adaa2-6ef9-4dd4-8344-6927575e06ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralCutoffGramBoundMixedBlockTwoLtTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralCutoffGramBoundMixedBlockTwoLtTopStatement
import Theorems.Thm_GlobalTheory_IntBall_lintegral_hB_one_two_lt_top


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
theorem _root_.solution : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | exact GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | (intros; apply GlobalTheory.IntBall.lintegral_hB_one_two_lt_top <;> assumption)
end _root_.GlobalTheory.T
