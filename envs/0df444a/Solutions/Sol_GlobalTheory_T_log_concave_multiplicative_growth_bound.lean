-- Prove2me | solution 1 for GlobalTheory.T.log_concave_multiplicative_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:29.491889+00:00
-- url     : https://prove2.me/submissions/927dc8e5-97c6-4e99-ab81-1a2872109365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBoundStatement
import Theorems.Thm_GlobalTheory_first_term_le_of_logConcave_blocks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  first | exact @GlobalTheory.first_term_le_of_logConcave_blocks | exact GlobalTheory.first_term_le_of_logConcave_blocks | (intros; apply GlobalTheory.first_term_le_of_logConcave_blocks <;> assumption)
end _root_.GlobalTheory.T
