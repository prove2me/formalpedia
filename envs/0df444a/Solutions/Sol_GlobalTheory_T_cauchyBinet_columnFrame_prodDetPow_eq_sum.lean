-- Prove2me | solution 1 for GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:29.382474+00:00
-- url     : https://prove2.me/submissions/35d26793-8822-4422-8b82-a571a62728a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
import Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_detG_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : GlobalTheory.MinorFrame.Var ι d a → ℂ), GlobalTheory.MinorFrame.rsub (GlobalTheory.MinorFrame.frameMat x₀).conjTranspose (GlobalTheory.MinorFrame.detG a n) = ∑ T : GlobalTheory.MinorFrame.Tup ι a d n, star (MvPolynomial.eval x₀ (GlobalTheory.MinorFrame.prodMinors T)) • GlobalTheory.MinorFrame.prodMinors T := by
  first | exact @GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | exact GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | (intros; apply GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum <;> assumption)
end _root_.GlobalTheory.T
