-- Prove2me | solution 1 for GlobalTheory.T.ae_transcendental_point_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:23.562429+00:00
-- url     : https://prove2.me/submissions/19495ca5-487f-48f4-8611-07c736f317b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishingStatement
import Theorems.Thm_P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  first | exact @GlobalTheory.ae_eval₂_ne_zero_of_countable | exact GlobalTheory.ae_eval₂_ne_zero_of_countable | (intros; apply GlobalTheory.ae_eval₂_ne_zero_of_countable <;> assumption)
end _root_.GlobalTheory.T
