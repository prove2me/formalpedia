-- Prove2me | solution 1 for GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:15.287148+00:00
-- url     : https://prove2.me/submissions/ae6e595f-cb53-4af6-a29a-839d74f1e398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffTsumOfLocallySummableBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffTsumOfLocallySummableBoundsStatement
import Theorems.Thm_GlobalTheory_contDiff_tsum_of_locally_summable_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  first | exact @GlobalTheory.contDiff_tsum_of_locally_summable_bounds | exact GlobalTheory.contDiff_tsum_of_locally_summable_bounds | (intros; apply GlobalTheory.contDiff_tsum_of_locally_summable_bounds <;> assumption)
end _root_.GlobalTheory.T
