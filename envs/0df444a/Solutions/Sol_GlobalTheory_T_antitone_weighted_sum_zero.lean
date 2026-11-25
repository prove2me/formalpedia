-- Prove2me | solution 1 for GlobalTheory.T.antitone_weighted_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:04.975968+00:00
-- url     : https://prove2.me/submissions/f2943c46-104a-4629-8c83-de1ab64e4bd5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneWeightedSumZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneWeightedSumZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Tempered_weighted_antitone_eq_zero_of_tails_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 → (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) → ∀ i, e i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | exact GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | (intros; apply GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg <;> assumption)
end _root_.GlobalTheory.T
