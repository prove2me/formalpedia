-- Prove2me | solution 1 for GlobalTheory.T.integers_bounded_archimedean_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:22.465458+00:00
-- url     : https://prove2.me/submissions/df77e7a3-f5c5-4b02-a0e9-9f162cea210c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCount
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCountStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IntCount_finite_and_ncard_le
import Theorems.Thm_UpperTheory_Reformulated_B_FiniteAndNcardBound_finite_and_ncard_le


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
    {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
    ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by
  first | exact @GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | exact GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | (intros; apply GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le <;> assumption)
end _root_.GlobalTheory.T
