-- Prove2me | solution 1 for GlobalTheory.T.count_bind_wordShuffle_by_positions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:44.13364+00:00
-- url     : https://prove2.me/submissions/10601dfa-f7fc-4501-92f4-259df89f0364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositionsStatement
import Theorems.Thm_GlobalTheory_ShufflePositions_count_bind_shuffle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A) (s₁ s₂ : Multiset (List A)), (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) = ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) * s₂.count (((List.finRange n).filter ε).map w) := by
  first | exact @GlobalTheory.ShufflePositions.count_bind_shuffle | exact GlobalTheory.ShufflePositions.count_bind_shuffle | (intros; apply GlobalTheory.ShufflePositions.count_bind_shuffle <;> assumption)
end _root_.GlobalTheory.T
